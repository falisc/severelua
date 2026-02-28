-- @ptacunit, build: ALPHA
local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 64) then
					if (Enum <= 31) then
						if (Enum <= 15) then
							if (Enum <= 7) then
								if (Enum <= 3) then
									if (Enum <= 1) then
										if (Enum > 0) then
											Stk[Inst[2]]();
										else
											Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
										end
									elseif (Enum > 2) then
										Stk[Inst[2]] = Stk[Inst[3]];
									elseif (Stk[Inst[2]] > Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum <= 5) then
									if (Enum == 4) then
										local A = Inst[2];
										local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
										local Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
									else
										Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
									end
								elseif (Enum > 6) then
									do
										return;
									end
								else
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum <= 11) then
								if (Enum <= 9) then
									if (Enum == 8) then
										Stk[Inst[2]] = Inst[3];
									else
										local A = Inst[2];
										do
											return Stk[A](Unpack(Stk, A + 1, Inst[3]));
										end
									end
								elseif (Enum > 10) then
									local A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
								else
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								end
							elseif (Enum <= 13) then
								if (Enum == 12) then
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								else
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								end
							elseif (Enum == 14) then
								Stk[Inst[2]] = not Stk[Inst[3]];
							else
								Stk[Inst[2]] = Inst[3] / Stk[Inst[4]];
							end
						elseif (Enum <= 23) then
							if (Enum <= 19) then
								if (Enum <= 17) then
									if (Enum > 16) then
										Stk[Inst[2]] = Stk[Inst[3]];
									elseif (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 18) then
									if (Stk[Inst[2]] > Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = VIP + Inst[3];
									end
								else
									local B = Stk[Inst[4]];
									if not B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 21) then
								if (Enum > 20) then
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								else
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								end
							elseif (Enum == 22) then
								if (Stk[Inst[2]] > Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = VIP + Inst[3];
								end
							else
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							end
						elseif (Enum <= 27) then
							if (Enum <= 25) then
								if (Enum > 24) then
									local B = Stk[Inst[4]];
									if not B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Inst[3] ~= 0;
								end
							elseif (Enum == 26) then
								Stk[Inst[2]] = Env[Inst[3]];
							elseif (Inst[2] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 29) then
							if (Enum == 28) then
								Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
							elseif (Inst[2] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 30) then
							local A = Inst[2];
							Stk[A] = Stk[A]();
						else
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
						end
					elseif (Enum <= 47) then
						if (Enum <= 39) then
							if (Enum <= 35) then
								if (Enum <= 33) then
									if (Enum > 32) then
										Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
									else
										for Idx = Inst[2], Inst[3] do
											Stk[Idx] = nil;
										end
									end
								elseif (Enum > 34) then
									if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = {};
								end
							elseif (Enum <= 37) then
								if (Enum > 36) then
									local A = Inst[2];
									local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									local A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
								end
							elseif (Enum == 38) then
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							elseif (Stk[Inst[2]] ~= Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 43) then
							if (Enum <= 41) then
								if (Enum > 40) then
									local A = Inst[2];
									local Cls = {};
									for Idx = 1, #Lupvals do
										local List = Lupvals[Idx];
										for Idz = 0, #List do
											local Upv = List[Idz];
											local NStk = Upv[1];
											local DIP = Upv[2];
											if ((NStk == Stk) and (DIP >= A)) then
												Cls[DIP] = NStk[DIP];
												Upv[1] = Cls;
											end
										end
									end
								else
									local B = Stk[Inst[4]];
									if B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								end
							elseif (Enum > 42) then
								Stk[Inst[2]] = Inst[3] / Stk[Inst[4]];
							elseif (Inst[2] < Stk[Inst[4]]) then
								VIP = Inst[3];
							else
								VIP = VIP + 1;
							end
						elseif (Enum <= 45) then
							if (Enum > 44) then
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							elseif (Stk[Inst[2]] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 46) then
							VIP = Inst[3];
						elseif (Stk[Inst[2]] <= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 55) then
						if (Enum <= 51) then
							if (Enum <= 49) then
								if (Enum == 48) then
									local A = Inst[2];
									local Index = Stk[A];
									local Step = Stk[A + 2];
									if (Step > 0) then
										if (Index > Stk[A + 1]) then
											VIP = Inst[3];
										else
											Stk[A + 3] = Index;
										end
									elseif (Index < Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								else
									local B = Inst[3];
									local K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
								end
							elseif (Enum == 50) then
								Stk[Inst[2]] = Inst[3];
							else
								do
									return Stk[Inst[2]];
								end
							end
						elseif (Enum <= 53) then
							if (Enum > 52) then
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
							else
								Stk[Inst[2]] = #Stk[Inst[3]];
							end
						elseif (Enum == 54) then
							do
								return Stk[Inst[2]];
							end
						else
							Stk[Inst[2]] = Upvalues[Inst[3]];
						end
					elseif (Enum <= 59) then
						if (Enum <= 57) then
							if (Enum == 56) then
								local A = Inst[2];
								Stk[A] = Stk[A]();
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum > 58) then
							if (Inst[2] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
						end
					elseif (Enum <= 61) then
						if (Enum > 60) then
							Stk[Inst[2]] = #Stk[Inst[3]];
						else
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
						end
					elseif (Enum <= 62) then
						Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
					elseif (Enum > 63) then
						Stk[Inst[2]][Inst[3]] = Inst[4];
					else
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
				elseif (Enum <= 97) then
					if (Enum <= 80) then
						if (Enum <= 72) then
							if (Enum <= 68) then
								if (Enum <= 66) then
									if (Enum == 65) then
										local A = Inst[2];
										local Step = Stk[A + 2];
										local Index = Stk[A] + Step;
										Stk[A] = Index;
										if (Step > 0) then
											if (Index <= Stk[A + 1]) then
												VIP = Inst[3];
												Stk[A + 3] = Index;
											end
										elseif (Index >= Stk[A + 1]) then
											VIP = Inst[3];
											Stk[A + 3] = Index;
										end
									else
										VIP = Inst[3];
									end
								elseif (Enum == 67) then
									local B = Stk[Inst[4]];
									if B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
								end
							elseif (Enum <= 70) then
								if (Enum > 69) then
									if (Stk[Inst[2]] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A = Inst[2];
									local Index = Stk[A];
									local Step = Stk[A + 2];
									if (Step > 0) then
										if (Index > Stk[A + 1]) then
											VIP = Inst[3];
										else
											Stk[A + 3] = Index;
										end
									elseif (Index < Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								end
							elseif (Enum == 71) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								local A = Inst[2];
								local T = Stk[A];
								for Idx = A + 1, Inst[3] do
									Insert(T, Stk[Idx]);
								end
							end
						elseif (Enum <= 76) then
							if (Enum <= 74) then
								if (Enum == 73) then
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								end
							elseif (Enum > 75) then
								if (Stk[Inst[2]] < Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							end
						elseif (Enum <= 78) then
							if (Enum > 77) then
								Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
							else
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							end
						elseif (Enum == 79) then
							local A = Inst[2];
							local Cls = {};
							for Idx = 1, #Lupvals do
								local List = Lupvals[Idx];
								for Idz = 0, #List do
									local Upv = List[Idz];
									local NStk = Upv[1];
									local DIP = Upv[2];
									if ((NStk == Stk) and (DIP >= A)) then
										Cls[DIP] = NStk[DIP];
										Upv[1] = Cls;
									end
								end
							end
						else
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
						end
					elseif (Enum <= 88) then
						if (Enum <= 84) then
							if (Enum <= 82) then
								if (Enum == 81) then
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								else
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
								end
							elseif (Enum > 83) then
								if (Inst[2] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]]();
							end
						elseif (Enum <= 86) then
							if (Enum > 85) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							else
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum > 87) then
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						else
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
						end
					elseif (Enum <= 92) then
						if (Enum <= 90) then
							if (Enum == 89) then
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							else
								local A = Inst[2];
								local C = Inst[4];
								local CB = A + 2;
								local Result = {Stk[A](Stk[A + 1], Stk[CB])};
								for Idx = 1, C do
									Stk[CB + Idx] = Result[Idx];
								end
								local R = Result[1];
								if R then
									Stk[CB] = R;
									VIP = Inst[3];
								else
									VIP = VIP + 1;
								end
							end
						elseif (Enum > 91) then
							Stk[Inst[2]] = {};
						else
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						end
					elseif (Enum <= 94) then
						if (Enum > 93) then
							local NewProto = Proto[Inst[3]];
							local NewUvals;
							local Indexes = {};
							NewUvals = Setmetatable({}, {__index=function(_, Key)
								local Val = Indexes[Key];
								return Val[1][Val[2]];
							end,__newindex=function(_, Key, Value)
								local Val = Indexes[Key];
								Val[1][Val[2]] = Value;
							end});
							for Idx = 1, Inst[4] do
								VIP = VIP + 1;
								local Mvm = Instr[VIP];
								if (Mvm[1] == 3) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						else
							Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
						end
					elseif (Enum <= 95) then
						Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
					elseif (Enum > 96) then
						Stk[Inst[2]][Inst[3]] = Inst[4];
					else
						local A = Inst[2];
						local Step = Stk[A + 2];
						local Index = Stk[A] + Step;
						Stk[A] = Index;
						if (Step > 0) then
							if (Index <= Stk[A + 1]) then
								VIP = Inst[3];
								Stk[A + 3] = Index;
							end
						elseif (Index >= Stk[A + 1]) then
							VIP = Inst[3];
							Stk[A + 3] = Index;
						end
					end
				elseif (Enum <= 113) then
					if (Enum <= 105) then
						if (Enum <= 101) then
							if (Enum <= 99) then
								if (Enum > 98) then
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									Upvalues[Inst[3]] = Stk[Inst[2]];
								end
							elseif (Enum > 100) then
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							else
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 103) then
							if (Enum > 102) then
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 104) then
							if (Inst[2] < Stk[Inst[4]]) then
								VIP = Inst[3];
							else
								VIP = VIP + 1;
							end
						else
							do
								return;
							end
						end
					elseif (Enum <= 109) then
						if (Enum <= 107) then
							if (Enum == 106) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							elseif (Stk[Inst[2]] > Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 108) then
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						elseif not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 111) then
						if (Enum == 110) then
							if (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Upvalues[Inst[3]] = Stk[Inst[2]];
						end
					elseif (Enum == 112) then
						local A = Inst[2];
						local B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
					else
						Stk[Inst[2]] = Upvalues[Inst[3]];
					end
				elseif (Enum <= 121) then
					if (Enum <= 117) then
						if (Enum <= 115) then
							if (Enum > 114) then
								if (Stk[Inst[2]] < Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum == 116) then
							local A = Inst[2];
							local C = Inst[4];
							local CB = A + 2;
							local Result = {Stk[A](Stk[A + 1], Stk[CB])};
							for Idx = 1, C do
								Stk[CB + Idx] = Result[Idx];
							end
							local R = Result[1];
							if R then
								Stk[CB] = R;
								VIP = Inst[3];
							else
								VIP = VIP + 1;
							end
						else
							local A = Inst[2];
							local T = Stk[A];
							local B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						end
					elseif (Enum <= 119) then
						if (Enum > 118) then
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = not Stk[Inst[3]];
						end
					elseif (Enum > 120) then
						Stk[Inst[2]] = Env[Inst[3]];
					else
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					end
				elseif (Enum <= 125) then
					if (Enum <= 123) then
						if (Enum > 122) then
							local NewProto = Proto[Inst[3]];
							local NewUvals;
							local Indexes = {};
							NewUvals = Setmetatable({}, {__index=function(_, Key)
								local Val = Indexes[Key];
								return Val[1][Val[2]];
							end,__newindex=function(_, Key, Value)
								local Val = Indexes[Key];
								Val[1][Val[2]] = Value;
							end});
							for Idx = 1, Inst[4] do
								VIP = VIP + 1;
								local Mvm = Instr[VIP];
								if (Mvm[1] == 3) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						else
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum > 124) then
						local A = Inst[2];
						do
							return Unpack(Stk, A, A + Inst[3]);
						end
					else
						local B = Inst[3];
						local K = Stk[B];
						for Idx = B + 1, Inst[4] do
							K = K .. Stk[Idx];
						end
						Stk[Inst[2]] = K;
					end
				elseif (Enum <= 127) then
					if (Enum == 126) then
						local A = Inst[2];
						local T = Stk[A];
						local B = Inst[3];
						for Idx = 1, B do
							T[Idx] = Stk[A + Idx];
						end
					else
						local A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
				elseif (Enum <= 128) then
					if (Stk[Inst[2]] ~= Inst[4]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum > 129) then
					if (Stk[Inst[2]] == Inst[4]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif Stk[Inst[2]] then
					VIP = VIP + 1;
				else
					VIP = Inst[3];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!EB3Q0003043Q0067616D65030A3Q004765745365727669636503073Q00506C6179657273030B3Q004C6F63616C506C6179657203103Q0055736572496E70757453657276696365030E3Q00466F72676F2Q74656E20442Q657003073Q00566563746F72332Q033Q006E6577021F85EB51B8FE57C002F853E3A51B10B3402Q022B8716D90E27C0030D3Q00416E6369656E742053616E6473024Q33B3E09BC002B81E85EB912DB14002FCA9F1D24DA22F40030C3Q0053756E6B656E2057696C647302736891ED7C40ADC0024Q33731DA340026891ED7CFFB2B3C0030C3Q0053706972697420522Q6F74730248E17A14AEFE994002378941602583AF4002F6285C8FC2E59DC0028Q00026Q005440026Q002440026Q000840027Q0040026Q003940026Q003E40030A3Q006C6F6164737472696E6703073Q00482Q747047657403443Q00682Q7470733A2Q2F7261772E67697468756275736572636F6E74656E742E636F6D2F7A2Q652D373635342F55492F726566732F68656164732F6D61696E2F55492E6C756103063Q006E6F74696679030C3Q004162792Q73616C204D656E7503093Q005549204C6F6164656403023Q00554903063Q0057696E646F7703053Q005469746C6503243Q004162792Q73616C204D656E75207C204275696C643A20416C706861207C204D617463686103043Q0053697A6503073Q00566563746F7232025Q00407F40025Q00E0754003043Q004F70656E2Q0103053Q005468656D6503063Q00476C6F62616C030B3Q004C69676874412Q63656E7403063Q00436F6C6F723303073Q0066726F6D524742025Q00806640026Q005940025Q00E06F4003063Q00412Q63656E74025Q00406040025Q00805140026Q006940030A3Q004461726B412Q63656E74026Q00444003093Q004C6967687442617365025Q0080414003043Q0042617365026Q003640026Q00324003083Q004461726B42617365026Q002E40026Q00284003043Q0054657874025Q00A06E40025Q00606D4003083Q00436F2Q6C61707365025Q00806B4003063Q00436F726E6572026Q00144003073Q0050612Q64696E67026Q0018402Q033Q0054616203043Q00486F6D6503073Q0053656374696F6E03043Q00496E666F03053Q004C6162656C03253Q0048652Q6C6F2C207468616E6B20796F7520666F72207573696E67206D79207363726970742E03173Q004D616465206279204070746163756E6974202F2066616C03303Q00646D204070746163756E697420666F7220616E7920692Q73756573202F2062756773202F2073752Q67657374696F6E7303083Q00496E7465726E616C03093Q00436F2Q6C617073656403113Q00506572666F726D616E636520537461747303063Q004D656D6F7279030A3Q004D656D6F72793A202Q2D2Q033Q0043505503073Q004350553A202Q2D2Q033Q0047505503073Q004750553A202Q2D03043Q007461736B03053Q00737061776E03073Q004661726D696E6703093Q004175746F204661726D03083Q00436865636B626F7803063Q00456E61626C6503073Q0044656661756C74010003073Q004B657962696E64030F3Q00546F2Q676C65204175746F6661726D2Q033Q004B657903043Q00456E756D03073Q004B6579436F646503013Q005003053Q00706169727303053Q007461626C6503063Q00696E7365727403083Q0044726F70646F776E03093Q004661726D204172656103073Q004F7074696F6E7303063Q00536C6964657203103Q004F787967656E205468726573686F6C642Q033Q004D696E2Q033Q004D617803043Q005374657003063Q0053752Q66697803013Q002503153Q004F787967656E205761726E696E672042752Q666572026Q003440026Q00F03F031D3Q004175746F2053652Q6C202872657175697265732067616D6570612Q732903053Q00437570696403063Q004C6F6E656C7903053Q005368696E7903043Q00502Q6F7003043Q00526F636B03053Q00436F72616C03043Q004D6F2Q7303053Q004D6574616C03043Q0053616E6403063Q00416C62696E6F030B3Q005472616E73706172656E7403063Q0043616374757303063Q0053706972697403063Q00466F2Q73696C03063Q00476F6C64656E03083Q004E6567617469766503053Q00466169727903093Q00496E76697369626C6503043Q004E656F6E030B3Q00556C74726176696F6C657403063Q00522Q6F74656403063Q00536861646F7703073Q00416E67656C696303073Q004162792Q73616C03083Q0047726F756E64656403063Q0042616E616E6103043Q004A61646503063Q004C6971756964030B3Q00466973682046696C74657203283Q0053656C656374206D75746174696F6E7320746F207461726765742028656D707479203D20612Q6C29030D3Q004D756C746944726F70646F776E03093Q004D75746174696F6E7303293Q0053656C656374206669736820747970657320746F207461726765742028656D707479203D20612Q6C29030C3Q00466973682054797065732031030D3Q00416E6369656E7420536861726B030A3Q00416E676C65726669736803093Q0042612Q726163756461030C3Q004269676D6F75746866697368030D3Q00426C61636B66696E2054756E6103083Q00426C6F626669736803093Q00426C75652054616E67030C3Q00426C756566696E2054756E6103083Q00436176656669736803093Q00436C6F776E666973682Q033Q00436F6403063Q00446973637573030A3Q00447261676F6E6669736803073Q004579656669736803073Q0047726F75706572030C3Q0048612Q6D657220536861726B03133Q00496E666C617465642050752Q66657266697368030C3Q004A616775617220536861726B03093Q004A652Q6C7966697368030F3Q004B696E6720416E676C65726669736803083Q004C696F6E6669736803093Q004D616869204D616869030C3Q00466973682054797065732032030A3Q004D6F736173617572757303083Q004E61706F6C656F6E03073Q004E61727768616C030F3Q00506163696669632046616E66697368030B3Q0050656C6963616E2045656C03073Q00506972616E686103073Q00506F6D70616E6F030A3Q0050752Q66657266697368030D3Q005361636162616D62617370697303083Q005361696C6669736803063Q0053616C6D6F6E030C3Q0053636F7270696F6E6669736803093Q0053656120486F727365030A3Q0053656120547572746C6503053Q00536861726B03053Q00537175696403073Q0053756E6669736803083Q0054616D626171756903043Q0054616E67030B3Q00546F7563616E204669736803053Q0054726F757403053Q005768616C65030D3Q0052657365742046696C7465727303063Q0042752Q746F6E032C3Q004661726D2053652Q74696E6773205B44616E6765726F75732C204564697420776974682043617574696F6E5D032D3Q0074772Q656E4475726174696F6E202D205365636F6E647320746F20436F6D706C65746520416E696D6174696F6E030E3Q0054772Q656E204475726174696F6E026Q00E03F03013Q007303153Q00526573657420746F2044656661756C74202833732903313Q007265747265617453702Q65644D756C7469706C696572202D204D756C7469706C69657320526574726561742053702Q656403133Q00526574726561742053702Q6564204D756C746903013Q007803153Q00526573657420746F2044656661756C74202832782903203Q006D696E44697374202D20466973682053682Q6F74696E672044697374616E6365030C3Q004D696E2044697374616E636503063Q00207374756473031B3Q00526573657420746F2044656661756C74202832352073747564732903233Q0074772Q656E5374657073202D20506F736974696F6E2055706461746520416D6F756E74030B3Q0054772Q656E20537465707303153Q00526573657420746F2044656661756C74202833302903083Q0054656C65706F727403093Q004C6F636174696F6E7303043Q004D69736303093Q005574696C697469657303213Q00546869732069732061206E6F636C697020616E7469636865617420627970612Q7303223Q00596F752077692Q6C206861766520746F2072656A6F696E20746F2064697361626C6503283Q005468657265666F726520796F752063612Q6E6F7420746F756368206C616E64206E6F722073652Q6C030E3Q00456E61626C65204E6F2D636C697003083Q0053652Q74696E6773030D3Q004D61696E2053652Q74696E6773030A3Q00546F2Q676C652047554903013Q004C00B7022Q00121A3Q00013Q0020705Q0002001232000200034Q003F3Q0002000200207800013Q000400121A000200013Q002070000200020002001232000400054Q003F0002000400022Q005C00033Q000400121A000400073Q002078000400040008001232000500093Q0012320006000A3Q0012320007000B4Q003F00040007000200100D00030006000400121A000400073Q0020780004000400080012320005000D3Q0012320006000E3Q0012320007000F4Q003F00040007000200100D0003000C000400121A000400073Q002078000400040008001232000500113Q001232000600123Q001232000700134Q003F00040007000200100D00030010000400121A000400073Q002078000400040008001232000500153Q001232000600163Q001232000700174Q003F00040007000200100D000300140004001232000400064Q00590005000300042Q001800065Q001232000700183Q001232000800193Q0012320009001A4Q0018000A6Q0018000B6Q0018000C6Q0050000D000D4Q005C000E5Q001232000F001B3Q0012320010001C3Q0012320011001D3Q0012320012001E4Q004E0013000F00122Q001800146Q005C00156Q005C00166Q005C00176Q005C00186Q005C00196Q005C001A6Q005C001B5Q00065E001C3Q000100042Q00033Q001A4Q00033Q001B4Q00033Q00154Q00033Q00163Q00065E001D0001000100052Q00033Q00154Q00033Q00164Q00033Q00194Q00033Q001A4Q00033Q001B3Q00022Q001E00023Q00065E001F0003000100012Q00033Q00013Q00065E00200004000100092Q00033Q000B4Q00033Q00014Q00033Q00124Q00033Q00134Q00033Q001E4Q00033Q00064Q00033Q000C4Q00033Q000E4Q00033Q001F3Q00065E00210005000100032Q00033Q00014Q00033Q001E4Q00033Q001F3Q00065E00220006000100042Q00033Q000D4Q00033Q00014Q00033Q000C4Q00033Q00063Q00121A0023001F3Q00121A002400013Q002070002400240020001232002600214Q006A002400264Q004A00233Q00022Q005300230001000100121A002300223Q001232002400233Q001232002500243Q0012320026001A4Q007F00230026000100121A002300253Q0020700023002300262Q005C00253Q000300306100250027002800121A0026002A3Q0020780026002600080012320027002B3Q0012320028002C4Q003F00260028000200100D0025002900260030610025002D002E2Q003F00230025000200207800240023002F00207800240024003000121A002500323Q002078002500250033001232002600343Q001232002700353Q001232002800364Q003F00250028000200100D00240031002500207800240023002F00207800240024003000121A002500323Q002078002500250033001232002600383Q001232002700393Q0012320028003A4Q003F00250028000200100D00240037002500207800240023002F00207800240024003000121A002500323Q002078002500250033001232002600193Q0012320027003C3Q001232002800384Q003F00250028000200100D0024003B002500207800240023002F00207800240024003000121A002500323Q0020780025002500330012320026003E3Q0012320027001E3Q0012320028003C4Q003F00250028000200100D0024003D002500207800240023002F00207800240024003000121A002500323Q002078002500250033001232002600403Q001232002700413Q0012320028001D4Q003F00250028000200100D0024003F002500207800240023002F00207800240024003000121A002500323Q002078002500250033001232002600433Q001232002700443Q001232002800414Q003F00250028000200100D00240042002500207800240023002F00207800240024003000121A002500323Q002078002500250033001232002600463Q001232002700473Q001232002800364Q003F00250028000200100D00240045002500207800240023002F00207800240024003000121A002500323Q0020780025002500330012320026003A3Q001232002700343Q001232002800494Q003F00250028000200100D00240048002500207800240023002F0020780024002400300030610024004A004B00207800240023002F0020780024002400300030610024004C004D00207000240023004E2Q005C00263Q000100306100260027004F2Q003F0024002600020020700025002400502Q005C00273Q00010030610027002700512Q003F0025002700020020700026002500522Q005C00283Q00010030610028002700532Q007F0026002800010020700026002500522Q005C00283Q00010030610028002700542Q007F0026002800010020700026002500522Q005C00283Q00010030610028002700552Q007F00260028000100207800260025005600306100260057002E0020700026002400502Q005C00283Q00010030610028002700582Q003F00260028000200207800270026005600306100270057002E2Q005C00273Q00030020700028002600522Q005C002A3Q0001003061002A0027005A2Q003F0028002A000200100D0027005900280020700028002600522Q005C002A3Q0001003061002A0027005C2Q003F0028002A000200100D0027005B00280020700028002600522Q005C002A3Q0001003061002A0027005E2Q003F0028002A000200100D0027005D002800121A0028005F3Q00207800280028006000065E00290007000100022Q00033Q00234Q00033Q00274Q002600280002000100207000280023004E2Q005C002A3Q0001003061002A002700612Q003F0028002A00020020700029002800502Q005C002B3Q0001003061002B002700622Q003F0029002B0002002070002A002900632Q005C002C3Q0002003061002C00270064003061002C0065006600065E002D0008000100062Q00033Q00064Q00033Q00014Q00033Q001F4Q00033Q001E4Q00033Q000B4Q00033Q000D4Q007F002A002D0001002070002A002900672Q005C002C3Q0002003061002C0027006800121A002D006A3Q002078002D002D006B002078002D002D006C00100D002C0069002D00065E002D0009000100062Q00033Q00064Q00033Q00014Q00033Q001F4Q00033Q001E4Q00033Q000B4Q00033Q000D3Q00022Q002E000A4Q007F002A002E00012Q005C002A5Q00121A002B006D4Q0011002C00034Q0064002B0002002D0004423Q00252Q0100121A0030006E3Q00207800300030006F2Q00110031002A4Q00110032002E4Q007F00300032000100065A002B00202Q0100020004423Q00202Q01002070002B002900702Q005C002D3Q0003003061002D0027007100100D002D0072002A00100D002D0065000400065E002E000B000100032Q00033Q00044Q00033Q00054Q00033Q00034Q007F002B002E0001002070002B002900732Q005C002D3Q0006003061002D00270074003061002D0075001A003061002D00760035003061002D0077004B00100D002D00650008003061002D0078007900065E002E000C000100012Q00033Q00084Q007F002B002E0001002070002B002900732Q005C002D3Q0006003061002D0027007A003061002D00750018003061002D0076007B003061002D0077007C003061002D0065001A003061002D0078007900065E002E000D000100012Q00033Q00094Q007F002B002E0001002070002B002900632Q005C002D3Q0002003061002D0027007D003061002D0065006600065E002E000E000100012Q00033Q00144Q007F002B002E00012Q005C002B00163Q001232002C007E3Q001232002D007F3Q001232002E00803Q001232002F00813Q001232003000823Q001232003100833Q001232003200843Q001232003300853Q001232003400863Q001232003500873Q001232003600883Q001232003700893Q0012320038008A3Q0012320039008B3Q001232003A008C3Q001232003B008D3Q001232003C008E3Q001232003D008F3Q001232003E00903Q001232003F00913Q001232004000923Q001232004100933Q001232004200943Q001232004300953Q001232004400963Q001232004500973Q001232004600983Q001232004700994Q0075002B001C00012Q0050002C002E3Q002070002F002800502Q005C00313Q000100306100310027009A2Q003F002F003100020020700030002F00522Q005C00323Q000100306100320027009B2Q007F0030003200010020700030002F009C2Q005C00323Q000300306100320027009D00100D00320072002B2Q005C00335Q00100D00320065003300065E0033000F000100032Q00033Q00154Q00033Q001C4Q00033Q00194Q003F0030003300022Q0011002C00303Q0020700030002F00522Q005C00323Q000100306100320027009E2Q007F0030003200010020700030002F009C2Q005C00323Q000300306100320027009F2Q005C003300133Q001232003400A03Q001232003500A13Q001232003600A23Q001232003700A33Q001232003800A43Q001232003900A53Q001232003A00A63Q001232003B00A73Q001232003C00A83Q001232003D00A93Q001232003E00AA3Q001232003F00AB3Q001232004000AC3Q001232004100AD3Q001232004200AE3Q001232004300AF3Q001232004400B03Q001232004500B13Q001232004600B23Q001232004700B33Q001232004800B43Q001232004900B54Q007500330016000100100D0032007200332Q005C00335Q00100D00320065003300065E00330010000100052Q00033Q00174Q00033Q00184Q00033Q00164Q00033Q001C4Q00033Q00194Q003F0030003300022Q0011002D00303Q0020700030002F009C2Q005C00323Q00030030610032002700B62Q005C003300133Q001232003400B73Q001232003500B83Q001232003600B93Q001232003700BA3Q001232003800BB3Q001232003900BC3Q001232003A00BD3Q001232003B00BE3Q001232003C00BF3Q001232003D00C03Q001232003E00C13Q001232003F00C23Q001232004000C33Q001232004100C43Q001232004200C53Q001232004300C63Q001232004400C73Q001232004500C83Q001232004600C93Q001232004700CA3Q001232004800CB3Q001232004900CC4Q007500330016000100100D0032007200332Q005C00335Q00100D00320065003300065E00330011000100052Q00033Q00184Q00033Q00174Q00033Q00164Q00033Q001C4Q00033Q00194Q003F0030003300022Q0011002E00303Q0020700030002F00522Q005C00323Q00010030610032002700CD2Q007F0030003200010020700030002F00CE2Q005C00323Q00010030610032002700CD00065E00330012000100092Q00033Q00154Q00033Q00174Q00033Q00184Q00033Q00164Q00033Q002C4Q00033Q002D4Q00033Q002E4Q00033Q001C4Q00033Q00194Q007F0030003300010020700030002800502Q005C00323Q00010030610032002700CF2Q003F0030003200020020700031003000522Q005C00333Q00010030610033002700D02Q007F0031003300010020700031003000732Q005C00333Q00060030610033002700D100306100330075007C00306100330076001A0030610033007700D200306100330065001B0030610033007800D300065E00340013000100032Q00033Q000F4Q00033Q00134Q00033Q00124Q003F0031003400020020700032003000CE2Q005C00343Q00010030610034002700D400065E00350014000100012Q00033Q00314Q007F0032003500010020700032003000522Q005C00343Q00010030610034002700D52Q007F0032003400010020700032003000732Q005C00343Q00060030610034002700D600306100340075007C00306100340076004B0030610034007700D200306100340065001C0030610034007800D700065E00350015000100012Q00033Q00104Q003F0032003500020020700033003000CE2Q005C00353Q00010030610035002700D800065E00360016000100012Q00033Q00324Q007F0033003600010020700033003000522Q005C00353Q00010030610035002700D92Q007F0033003500010020700033003000732Q005C00353Q00060030610035002700DA00306100350075004B00306100350076003500306100350077004B00306100350065003C0030610035007800DB00065E00360017000100012Q00033Q00114Q003F0033003600020020700034003000CE2Q005C00363Q00010030610036002700DC00065E00370018000100012Q00033Q00334Q007F0034003700010020700034003000522Q005C00363Q00010030610036002700DD2Q007F0034003600010020700034003000732Q005C00363Q00050030610036002700DE00306100360075001A00306100360076003500306100360077004B00306100360065001E00065E00370019000100032Q00033Q00124Q00033Q00134Q00033Q000F4Q003F0034003700020020700035003000CE2Q005C00373Q00010030610037002700DF00065E0038001A000100012Q00033Q00344Q007F00350038000100207000350023004E2Q005C00373Q00010030610037002700E02Q003F0035003700020020700036003500502Q005C00383Q00010030610038002700E12Q003F00360038000200121A0037006D4Q0011003800034Q00640037000200390004423Q00530201002070003C003600CE2Q005C003E3Q000100100D003E0027003A00065E003F001B000100032Q00033Q00214Q00033Q003B4Q00033Q003A4Q007F003C003F00012Q0029003A5Q00065A0037004A020100020004423Q004A020100207000370023004E2Q005C00393Q00010030610039002700E22Q003F0037003900020020700038003700502Q005C003A3Q0001003061003A002700E32Q003F0038003A00020020700039003800522Q005C003B3Q0001003061003B002700E42Q007F0039003B00010020700039003800522Q005C003B3Q0001003061003B002700E52Q007F0039003B00010020700039003800522Q005C003B3Q0001003061003B002700E62Q007F0039003B00010020700039003800CE2Q005C003B3Q0001003061003B002700E700065E003C001C000100012Q00033Q00014Q007F0039003C000100207000390023004E2Q005C003B3Q0001003061003B002700E82Q003F0039003B0002002070003A003900502Q005C003C3Q0001003061003C002700E92Q003F003A003C0002002070003B003A00672Q005C003D3Q0002003061003D002700EA00121A003E006A3Q002078003E003E006B002078003E003E00EB00100D003D0069003E00065E003E001D000100012Q00033Q00233Q00022Q003F001E4Q007F003B003F000100121A003B005F3Q002078003B003B006000065E003C001F0001000A2Q00033Q00064Q00033Q000A4Q00033Q000C4Q00033Q00014Q00033Q000E4Q00033Q001D4Q00033Q00074Q00033Q00084Q00033Q00094Q00033Q000D4Q0026003B0002000100121A003B005F3Q002078003B003B006000065E003C0020000100052Q00033Q000C4Q00033Q00064Q00033Q000D4Q00033Q000A4Q00033Q00014Q0026003B0002000100121A003B005F3Q002078003B003B006000065E003C0021000100032Q00033Q00064Q00033Q000C4Q00033Q00014Q0026003B0002000100121A003B005F3Q002078003B003B006000065E003C0022000100122Q00033Q00064Q00033Q000B4Q00033Q000C4Q00033Q00014Q00033Q00074Q00033Q00084Q00033Q00094Q00033Q000A4Q00033Q00144Q00033Q00224Q00033Q000D4Q00033Q00204Q00033Q00054Q00033Q00134Q00033Q00104Q00033Q001D4Q00033Q00194Q00033Q00114Q0026003B000200012Q00073Q00013Q00233Q00023Q0003063Q006970616972732Q0100154Q005C8Q00628Q005C8Q00623Q00013Q00121A3Q00014Q0037000100024Q00643Q000200020004423Q000A00012Q003700055Q00202100050004000200065A3Q0008000100020004423Q0008000100121A3Q00014Q0037000100034Q00643Q000200020004423Q001200012Q0037000500013Q00202100050004000200065A3Q0010000100020004423Q001000012Q00073Q00017Q000D3Q00028Q00030E3Q0046696E6446697273744368696C6403043Q004865616403083Q00522Q6F7450617274010003053Q00737461747303043Q004669736803083Q004D75746174696F6E03053Q004C6162656C03083Q00666973685479706503043Q0054657874030C3Q00666973684D75746174696F6E3Q01634Q003700016Q003D000100013Q000E6900010005000100010004423Q000500012Q003C00016Q0018000100014Q0037000200014Q003D000200023Q000E690001000B000100020004423Q000B00012Q003C00026Q0018000200013Q00064900010012000100010004423Q0012000100064900020012000100010004423Q001200012Q0018000300014Q0036000300024Q0037000300024Q0059000300033Q00064900030048000100010004423Q0048000100207000043Q0002001232000600034Q003F0004000600020006490004001E000100010004423Q001E000100207000043Q0002001232000600044Q003F00040006000200064900040024000100010004423Q002400012Q0037000500023Q00202100053Q00052Q001800056Q0036000500023Q002070000500040002001232000700064Q003F0005000700020006490005002D000100010004423Q002D00012Q0037000600023Q00202100063Q00052Q001800066Q0036000600023Q002070000600050002001232000800074Q003F000600080002002070000700050002001232000900084Q003F00070009000200064300080038000100070004423Q00380001002070000800070002001232000A00094Q003F0008000A00020006770006003C00013Q0004423Q003C000100064900080040000100010004423Q004000012Q0037000900023Q00202100093Q00052Q001800096Q0036000900024Q005C00093Q0002002078000A0006000B00100D0009000A000A002078000A0008000B00100D0009000C000A2Q0011000300094Q0037000900024Q002D00093Q00030026820003004C000100050004423Q004C00012Q001800046Q0036000400023Q0006770001005400013Q0004423Q005400012Q0037000400033Q00207800050003000C2Q0059000400040005002680000400540001000D0004423Q005400012Q003C00046Q0018000400013Q0006770002005D00013Q0004423Q005D00012Q0037000500043Q00207800060003000A2Q00590005000500060026800005005D0001000D0004423Q005D00012Q003C00056Q0018000500013Q00064300060061000100040004423Q006100012Q0011000600054Q0036000600024Q00073Q00017Q00073Q0003063Q00747970656F6603083Q00496E7374616E636503063Q00697061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103083Q004261736550617274030A3Q0043616E436F2Q6C696465021B3Q0006773Q000700013Q0004423Q0007000100121A000200014Q001100036Q005800020002000200268000020008000100020004423Q000800012Q00073Q00013Q00121A000200033Q00207000033Q00042Q0063000300044Q000400023Q00040004423Q0018000100121A000700014Q0011000800064Q005800070002000200268200070018000100020004423Q00180001002070000700060005001232000900064Q003F0007000900020006770007001800013Q0004423Q0018000100100D00060007000100065A0002000D000100020004423Q000D00012Q00073Q00017Q00073Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403163Q00412Q73656D626C794C696E65617256656C6F6369747903073Q00566563746F72332Q033Q006E6577028Q0001143Q0006130001000400013Q0004423Q000400012Q003700015Q00207800010001000100064900010007000100010004423Q000700012Q00073Q00013Q002070000200010002001232000400034Q003F0002000400020006770002001300013Q0004423Q0013000100121A000300053Q002078000300030006001232000400073Q001232000500073Q001232000600074Q003F00030006000200100D0002000400032Q00073Q00017Q00283Q0003063Q00506172656E7403043Q007761726E03343Q005B4162792Q73616C5D20736D2Q6F74684D6F7665546F3A20722Q6F74206973206E696C206F7220686173206E6F20706172656E7403093Q0043686172616374657203083Q00506F736974696F6E028Q00026Q00F03F033D3Q005B4162792Q73616C5D20736D2Q6F74684D6F7665546F3A2064657374506F73206F722063752Q72656E74506F73206973206E696C206174207374657020027Q004003063Q00747970656F6603073Q00566563746F723303093Q004D61676E6974756465026Q00244003063Q006E756D626572026Q00E03F032B3Q005B4162792Q73616C5D20736D2Q6F74684D6F7665546F3A20737475636B20646574656374656420666F722003083Q00746F737472696E67030E3Q00207C206D6F766564446973743A2003083Q00536166655A6F6E652Q0103043Q007461736B03053Q0064656C6179026Q002E4003013Q005803013Q005903013Q005A03043Q006D61746803043Q00737172742Q033Q006E657703093Q00776F726B737061636503043Q0047616D6503053Q005475626573030E3Q0046696E6446697273744368696C6403043Q004E616D6503083Q00522Q6F7450617274025Q00804640026Q00144003053Q007063612Q6C030B3Q006D6F75736531636C69636B03043Q007761697406CB3Q0006773Q000500013Q0004423Q0005000100207800063Q00010006490006000B000100010004423Q000B000100121A000600023Q001232000700034Q00260006000200012Q001800066Q006200066Q00073Q00014Q0037000600013Q00207800060006000400061300070010000100030004423Q001000012Q0037000700023Q00061300080013000100040004423Q001300012Q0037000800033Q00207800093Q0005001232000A00064Q0018000B00014Q0062000B6Q0037000B00044Q0011000C00064Q0018000D6Q007F000B000D0001001232000B00074Q0011000C00073Q001232000D00073Q000445000B00BF00012Q0037000F00053Q000677000F00BF00013Q0004423Q00BF00012Q0037000F5Q000677000F00BF00013Q0004423Q00BF00012Q0037000F00063Q000677000F002900013Q0004423Q002900010004423Q00BF00012Q0011000F00014Q001F000F0001000200207800103Q0005000677000F003000013Q0004423Q0030000100064900100036000100010004423Q0036000100121A001100023Q001232001200084Q00110013000E4Q007C0012001200132Q00260011000200010004423Q00BF00012Q003E000A000A0008000E54000900680001000A0004423Q00680001001232001100063Q00121A0012000A4Q0011001300104Q0058001200020002002682001200470001000B0004423Q0047000100121A0012000A4Q0011001300094Q0058001200020002002682001200470001000B0004423Q004700012Q001500120010000900207800110012000C0004423Q004800010012320011000D3Q00121A0012000A4Q0011001300114Q0058001200020002002682001200660001000E0004423Q00660001002673001100660001000F0004423Q0066000100121A001200023Q001232001300103Q00121A001400114Q0011001500054Q0058001400020002001232001500124Q0011001600114Q007C0013001300162Q0026001200020001000677000500BF00013Q0004423Q00BF0001002680000500BF000100130004423Q00BF00012Q0037001200073Q00202100120005001400121A001200153Q002078001200120016001232001300173Q00065E00143Q000100022Q00713Q00074Q00033Q00054Q007F0012001400010004423Q00BF00012Q0011000900103Q001232000A00063Q0020780011000F00180020780012001000182Q00150011001100120020780012000F00190020780013001000192Q00150012001200130020780013000F001A00207800140010001A2Q001500130013001400121A0014001B3Q00207800140014001C2Q00520015001100112Q00520016001200122Q003E0015001500162Q00520016001300132Q003E0015001500162Q00580014000200020006770002008100013Q0004423Q008100012Q0011001500024Q0011001600144Q00580015000200020006770015008100013Q0004423Q008100010004423Q00BF00012Q001500150007000E00204B00150015000700100F00150007001500121A0016000B3Q00207800160016001D0020780017001000180020780018000F00180020780019001000182Q00150018001800192Q00520018001800152Q003E0017001700180020780018001000190020780019000F0019002078001A001000192Q001500190019001A2Q00520019001900152Q003E00180018001900207800190010001A002078001A000F001A002078001B0010001A2Q0015001A001A001B2Q0052001A001A00152Q003E00190019001A2Q003F0016001900022Q0037001700084Q0011001800064Q002600170002000100100D3Q0005001600121A0017001E3Q00207800170017001F0020780017001700200020700017001700212Q0037001900013Q0020780019001900222Q003F001700190002000677001700AD00013Q0004423Q00AD0001002070001800170021001232001A00234Q003F0018001A0002000677001800AD00013Q0004423Q00AD000100207800180017002300100D00180005001600121A0018001B3Q00207800180018001C2Q00520019001100112Q0052001A001300132Q003E00190019001A2Q0058001800020002002673001400BA000100240004423Q00BA0001000E1B002500BA000100180004423Q00BA000100121A001900263Q00121A001A00274Q002600190002000100121A001900153Q0020780019001900282Q0011001A00084Q0026001900020001000441000B001F00012Q0037000B00084Q0037000C00013Q002078000C000C00042Q0026000B000200012Q0037000B00044Q0037000C00013Q002078000C000C00042Q0018000D00014Q007F000B000D00012Q0018000B6Q0062000B6Q00073Q00013Q00013Q00015Q00044Q00378Q0037000100013Q0020213Q000100012Q00073Q00017Q001A3Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403043Q007761726E03303Q005B4162792Q73616C5D2074656C65706F7274546F3A2048756D616E6F6964522Q6F7450617274206E6F7420666F756E6403083Q00506F736974696F6E03013Q005803013Q005903013Q005A03043Q006D61746803043Q0073717274026Q0008402Q033Q006D6178026Q00244003053Q00666C2Q6F7202FCA9F1D24D62903F026Q00F03F03073Q00566563746F72332Q033Q006E657703093Q00776F726B737061636503043Q0047616D6503053Q00547562657303043Q004E616D6503083Q00522Q6F745061727403043Q007461736B03043Q007761697402764Q003700025Q00207800020002000100064300030007000100020004423Q00070001002070000300020002001232000500034Q003F0003000500020006490003000D000100010004423Q000D000100121A000400043Q001232000500054Q00260004000200012Q00073Q00014Q0037000400014Q0011000500024Q001800066Q007F00040006000100207800040003000600207800053Q00070020780006000400072Q001500050005000600207800063Q00080020780007000400082Q001500060006000700207800073Q00090020780008000400092Q001500070007000800121A0008000A3Q00207800080008000B2Q00520009000500052Q0052000A000600062Q003E00090009000A2Q0052000A000700072Q003E00090009000A2Q00580008000200020012320009000C3Q00121A000A000A3Q002078000A000A000D001232000B000E3Q00121A000C000A3Q002078000C000C000F2Q004E000D000800092Q0063000C000D4Q004A000A3Q0002001232000B00103Q001232000C00114Q0011000D000A3Q001232000E00113Q000445000C006000012Q004E0010000F000A00121A001100123Q00207800110011001300207800120004000700207800133Q00070020780014000400072Q00150013001300142Q00520013001300102Q003E00120012001300207800130004000800207800143Q00080020780015000400082Q00150014001400152Q00520014001400102Q003E00130013001400207800140004000900207800153Q00090020780016000400092Q00150015001500162Q00520015001500102Q003E0014001400152Q003F0011001400022Q0037001200024Q0011001300024Q002600120002000100100D00030006001100121A001200143Q0020780012001200150020780012001200160020700012001200022Q003700145Q0020780014001400172Q003F0012001400020006770012005B00013Q0004423Q005B0001002070001300120002001232001500184Q003F0013001500020006770013005B00013Q0004423Q005B000100207800130012001800100D00130006001100121A001300193Q00207800130013001A2Q00110014000B4Q0026001300020001000441000C0031000100100D000300063Q00121A000C00143Q002078000C000C0015002078000C000C0016002070000C000C00022Q0037000E5Q002078000E000E00172Q003F000C000E0002000677000C007100013Q0004423Q00710001002070000D000C0002001232000F00184Q003F000D000F0002000677000D007100013Q0004423Q00710001002078000D000C001800100D000D00064Q0037000D00014Q0011000E00024Q0018000F00014Q007F000D000F00012Q00073Q00017Q000F3Q00030A3Q006B657972656C65617365025Q0040524003043Q007461736B03043Q0077616974026Q33C33F03083Q006B65797072652Q73025Q00C05340029A5Q99B93F027B14AE47E17AB43F029A5Q99C93F025Q00C05140026Q00E03F03053Q007063612Q6C029A5Q99D93F026Q33D33F00574Q00627Q00121A3Q00013Q001232000100024Q00263Q0002000100121A3Q00033Q0020785Q0004001232000100054Q00263Q0002000100121A3Q00063Q001232000100074Q00263Q0002000100121A3Q00033Q0020785Q0004001232000100084Q00263Q0002000100121A3Q00013Q001232000100074Q00263Q0002000100121A3Q00033Q0020785Q0004001232000100094Q00263Q0002000100121A3Q00063Q001232000100074Q00263Q0002000100121A3Q00033Q0020785Q0004001232000100084Q00263Q0002000100121A3Q00013Q001232000100074Q00263Q0002000100121A3Q00033Q0020785Q00040012320001000A4Q00263Q0002000100121A3Q00063Q0012320001000B4Q00263Q0002000100121A3Q00033Q0020785Q0004001232000100084Q00263Q0002000100121A3Q00013Q0012320001000B4Q00263Q0002000100121A3Q00033Q0020785Q00040012320001000C4Q00263Q0002000100121A3Q000D3Q00065E00013Q000100012Q00713Q00014Q00643Q000200010006493Q0038000100010004423Q0038000100121A000200033Q0020780002000200040012320003000E4Q002600020002000100121A000200063Q0012320003000B4Q002600020002000100121A000200033Q002078000200020004001232000300084Q002600020002000100121A000200013Q0012320003000B4Q002600020002000100121A000200033Q0020780002000200040012320003000F4Q00260002000200012Q001800026Q0062000200023Q00121A000200033Q0020780002000200040012320003000A4Q00260002000200012Q0037000200033Q0006770002005600013Q0004423Q0056000100121A000200063Q001232000300024Q00260002000200012Q00073Q00013Q00013Q00193Q0003093Q00506C6179657247756903043Q004D61696E03083Q004261636B7061636B03043Q004C697374030A3Q0047616D6570612Q73657303043Q0053652Q6C03073Q00412Q6472652Q73026Q007140030B3Q006D656D6F72795F7265616403053Q00666C6F6174026Q00104003043Q006D61746803053Q00666C2Q6F72026Q003440030C3Q006D6F7573656D6F766561627303043Q007461736B03043Q0077616974029A5Q99A93F026Q00F03F03063Q0072616E646F6D027Q00C0027Q0040027B14AE47E17AA43F029A5Q99B93F030B3Q006D6F75736531636C69636B00454Q00377Q0020785Q00010020785Q00020020785Q00030020785Q00040020785Q00050020785Q000600207800013Q000700204B00010001000800121A000200093Q0012320003000A4Q0011000400014Q003F00020004000200121A000300093Q0012320004000A3Q00204B00050001000B2Q003F00030005000200121A0004000C3Q00207800040004000D2Q0011000500024Q005800040002000200204B00040004000E00121A0005000C3Q00207800050005000D2Q0011000600034Q005800050002000200204B00050005000E00121A0006000F4Q0011000700044Q0011000800054Q007F00060008000100121A000600103Q002078000600060011001232000700124Q0026000600020001001232000600133Q0012320007000B3Q001232000800133Q0004450006003A000100121A000A000F3Q00121A000B000C3Q002078000B000B0014001232000C00153Q001232000D00164Q003F000B000D00022Q003E000B0004000B00121A000C000C3Q002078000C000C0014001232000D00153Q001232000E00164Q003F000C000E00022Q003E000C0005000C2Q007F000A000C000100121A000A00103Q002078000A000A0011001232000B00174Q0026000A0002000100044100060027000100121A0006000F4Q0011000700044Q0011000800054Q007F00060008000100121A000600103Q002078000600060011001232000700184Q002600060002000100121A000600194Q00530006000100012Q00073Q00017Q000D3Q0003043Q0067616D65030A3Q004765745365727669636503053Q00537461747303103Q00506572666F726D616E6365537461747303053Q007061697273030B3Q004765744368696C6472656E03043Q004E616D6503083Q00496E7465726E616C03073Q0052752Q6E696E6703043Q007461736B03043Q0077616974026Q00F03F03053Q007063612Q6C00213Q00121A3Q00013Q0020705Q0002001232000200034Q003F3Q000200020020785Q00042Q005C00015Q00121A000200053Q00207000033Q00062Q0063000300044Q000400023Q00040004423Q000D00010020780007000600072Q002D00010007000600065A0002000B000100020004423Q000B000100065E00023Q000100012Q00033Q00014Q003700035Q0020780003000300080020780003000300090006770003002000013Q0004423Q0020000100121A0003000A3Q00207800030003000B0012320004000C4Q002600030002000100121A0003000D3Q00065E00040001000100022Q00713Q00014Q00033Q00024Q00260003000200010004423Q001100012Q00073Q00013Q00023Q00073Q002Q033Q004E2F4103073Q00412Q6472652Q73030B3Q006D656D6F72795F7265616403063Q00737472696E67026Q006A40028Q00026Q006B40011A4Q003700016Q0059000100013Q00064900010006000100010004423Q00060001001232000200014Q0036000200023Q00207800020001000200121A000300033Q001232000400043Q00204B0005000200052Q003F0003000500020006770003001100013Q0004423Q001100012Q003D000400033Q000E1B00060011000100040004423Q001100012Q0036000300023Q00121A000400033Q001232000500043Q00204B0006000200072Q003F00040006000200061300050018000100040004423Q00180001001232000500014Q0036000500024Q00073Q00017Q00073Q0003063Q004D656D6F72792Q033Q0053657403083Q004D656D6F72793A202Q033Q0043505503053Q004350553A202Q033Q0047505503053Q004750553A20001C4Q00377Q0020785Q00010020705Q0002001232000200034Q0037000300013Q001232000400014Q00580003000200022Q007C0002000200032Q007F3Q000200012Q00377Q0020785Q00040020705Q0002001232000200054Q0037000300013Q001232000400044Q00580003000200022Q007C0002000200032Q007F3Q000200012Q00377Q0020785Q00060020705Q0002001232000200074Q0037000300013Q001232000400064Q00580003000200022Q007C0002000200032Q007F3Q000200012Q00073Q00017Q00033Q0003093Q00436861726163746572030A3Q006B657972656C65617365025Q0040524001174Q00628Q003700015Q00064900010016000100010004423Q001600012Q0037000100013Q0020780001000100010006770001001600013Q0004423Q0016000100121A000100023Q001232000200034Q00260001000200012Q0037000100024Q00530001000100012Q0037000100034Q0037000200013Q0020780002000200012Q0018000300014Q007F0001000300012Q001800016Q0062000100044Q0050000100014Q0062000100054Q00073Q00017Q00033Q0003093Q00436861726163746572030A3Q006B657972656C65617365025Q0040524000194Q00378Q000E8Q00628Q00377Q0006493Q0018000100010004423Q001800012Q00373Q00013Q0020785Q00010006773Q001800013Q0004423Q0018000100121A3Q00023Q001232000100034Q00263Q000200012Q00373Q00024Q00533Q000100012Q00373Q00034Q0037000100013Q0020780001000100012Q0018000200014Q007F3Q000200012Q00188Q00623Q00044Q00508Q00623Q00054Q00073Q00019Q002Q002Q014Q00073Q00019Q002Q0001064Q00628Q0037000100024Q003700026Q00590001000100022Q0062000100014Q00073Q00019Q002Q0001024Q00628Q00073Q00019Q002Q0001024Q00628Q00073Q00019Q002Q0001024Q00628Q00073Q00017Q00013Q00028Q00010A4Q00628Q0037000100014Q00530001000100012Q005C00016Q0062000100024Q003D00015Q00268200010009000100010004423Q000900010004423Q000900012Q00073Q00017Q00043Q0003063Q0069706169727303053Q007461626C6503063Q00696E73657274028Q0001224Q00628Q005C00015Q00121A000200014Q003700036Q00640002000200040004423Q000B000100121A000700023Q0020780007000700032Q0011000800014Q0011000900064Q007F00070009000100065A00020006000100020004423Q0006000100121A000200014Q0037000300014Q00640002000200040004423Q0016000100121A000700023Q0020780007000700032Q0011000800014Q0011000900064Q007F00070009000100065A00020011000100020004423Q001100012Q0062000100024Q0037000200034Q00530002000100012Q005C00026Q0062000200044Q003D000200013Q00268200020021000100040004423Q002100010004423Q002100012Q00073Q00017Q00043Q0003063Q0069706169727303053Q007461626C6503063Q00696E73657274028Q0001224Q00628Q005C00015Q00121A000200014Q0037000300014Q00640002000200040004423Q000B000100121A000700023Q0020780007000700032Q0011000800014Q0011000900064Q007F00070009000100065A00020006000100020004423Q0006000100121A000200014Q003700036Q00640002000200040004423Q0016000100121A000700023Q0020780007000700032Q0011000800014Q0011000900064Q007F00070009000100065A00020011000100020004423Q001100012Q0062000100024Q0037000200034Q00530002000100012Q005C00026Q0062000200044Q003D000200013Q00268200020021000100040004423Q002100010004423Q002100012Q00073Q00017Q00013Q002Q033Q0053657400224Q005C8Q00628Q005C8Q00623Q00014Q005C8Q00623Q00024Q005C8Q00623Q00034Q00373Q00043Q0006773Q000F00013Q0004423Q000F00012Q00373Q00043Q0020705Q00012Q005C00026Q007F3Q000200012Q00373Q00053Q0006773Q001600013Q0004423Q001600012Q00373Q00053Q0020705Q00012Q005C00026Q007F3Q000200012Q00373Q00063Q0006773Q001D00013Q0004423Q001D00012Q00373Q00063Q0020705Q00012Q005C00026Q007F3Q000200012Q00373Q00074Q00533Q000100012Q005C8Q00623Q00084Q00073Q00019Q002Q0001064Q00628Q003700016Q0037000200024Q004E0001000100022Q0062000100014Q00073Q00017Q00023Q002Q033Q00536574026Q00084000054Q00377Q0020705Q0001001232000200024Q007F3Q000200012Q00073Q00019Q002Q0001024Q00628Q00073Q00017Q00023Q002Q033Q00536574027Q004000054Q00377Q0020705Q0001001232000200024Q007F3Q000200012Q00073Q00019Q002Q0001024Q00628Q00073Q00017Q00023Q002Q033Q00536574026Q00444000054Q00377Q0020705Q0001001232000200024Q007F3Q000200012Q00073Q00019Q002Q0001064Q00628Q0037000100024Q003700026Q004E0001000100022Q0062000100014Q00073Q00017Q00023Q002Q033Q00536574026Q003E4000054Q00377Q0020705Q0001001232000200024Q007F3Q000200012Q00073Q00017Q00023Q0003043Q007461736B03053Q00737061776E00083Q00121A3Q00013Q0020785Q000200065E00013Q000100032Q00718Q00713Q00014Q00713Q00024Q00263Q000200012Q00073Q00013Q00018Q00054Q00378Q0037000100014Q0037000200024Q007F3Q000200012Q00073Q00017Q00023Q0003043Q007461736B03053Q00737061776E00063Q00121A3Q00013Q0020785Q000200065E00013Q000100012Q00718Q00263Q000200012Q00073Q00013Q00013Q00173Q0003093Q00776F726B7370616365030E3Q0046696E6446697273744368696C642Q033Q004D617003063Q00646562726973030E3Q0047657444657363656E64616E7473026Q00F03F2Q033Q0049734103083Q004261736550617274030A3Q0043616E436F2Q6C696465010003053Q007063612Q6C03063Q00506172656E74025Q00408F40028Q0003043Q007461736B03043Q007761697403043Q007761726E03203Q005B4162792Q73616C5D204E6F2D636C69703A204D6170206E6F7420666F756E6403093Q0043686172616374657203063Q0069706169727303043Q0047616D6503053Q00547562657303043Q004E616D6500543Q00121A3Q00013Q0020705Q0002001232000200034Q003F3Q0002000200121A000100013Q002070000100010002001232000300044Q003F0001000300020006773Q002700013Q0004423Q002700010006770001002700013Q0004423Q0027000100207000023Q00052Q0058000200020002001232000300064Q003D000400023Q001232000500063Q0004450003002600012Q0059000700020006002070000800070007001232000A00084Q003F0008000A00020006770008001E00013Q0004423Q001E000100306100070009000A00121A0008000B3Q00065E00093Q000100012Q00033Q00074Q002600080002000100100D0007000C000100206700080006000D002682000800240001000E0004423Q0024000100121A0008000F3Q0020780008000800102Q00530008000100012Q002900075Q0004410003001200010004423Q002A000100121A000200113Q001232000300124Q00260002000200012Q003700025Q0020780002000200130006770002003D00013Q0004423Q003D000100121A000200144Q003700035Q0020780003000300130020700003000300052Q0063000300044Q000400023Q00040004423Q003B0001002070000700060007001232000900084Q003F0007000900020006770007003B00013Q0004423Q003B000100306100060009000A00065A00020035000100020004423Q0035000100121A000200013Q0020780002000200150020780002000200160020700002000200022Q003700045Q0020780004000400172Q003F0002000400020006770002005300013Q0004423Q0053000100121A000300143Q0020700004000200052Q0063000400054Q000400033Q00050004423Q00510001002070000800070007001232000A00084Q003F0008000A00020006770008005100013Q0004423Q0051000100306100070009000A00065A0003004B000100020004423Q004B00012Q00073Q00013Q00013Q00033Q0003083Q0043616E5175657279010003083Q0043616E546F75636800054Q00377Q0030613Q000100022Q00377Q0030613Q000300022Q00073Q00017Q00013Q0003063Q00546F2Q676C6500044Q00377Q0020705Q00012Q00263Q000200012Q00073Q00019Q002Q002Q014Q00073Q00017Q001B3Q0003043Q007461736B03043Q0077616974026Q00E03F03093Q00776F726B737061636503043Q0047616D6503043Q0046697368030E3Q0046696E6446697273744368696C6403063Q00636C69656E7403093Q0043686172616374657203103Q0048756D616E6F6964522Q6F745061727403083Q00506F736974696F6E024Q007E842E41028Q0003063Q00697061697273030B3Q004765744368696C6472656E026Q00F03F03043Q004E616D6503043Q004865616403083Q00522Q6F7450617274030B3Q005072696D6172795061727403013Q005803013Q005903013Q005A03043Q006D61746803043Q0073717274026Q003E4003053Q007063612Q6C00853Q00121A3Q00013Q0020785Q0002001232000100034Q00263Q000200012Q00377Q0006775Q00013Q0004425Q00012Q00373Q00013Q0006495Q000100010004425Q00012Q00373Q00023Q0006773Q000E00013Q0004423Q000E00010004425Q000100121A3Q00043Q0020785Q00050020785Q00060006773Q001900013Q0004423Q0019000100121A3Q00043Q0020785Q00050020785Q00060020705Q0007001232000200084Q003F3Q000200020006493Q001C000100010004423Q001C00010004425Q00012Q0037000100033Q00207800010001000900064300020023000100010004423Q002300010020700002000100070012320004000A4Q003F00020004000200064900020026000100010004423Q002600010004425Q000100207800030002000B2Q0050000400043Q0012320005000C3Q0012320006000D3Q0012320007000D3Q0012320008000D3Q00121A0009000E3Q002070000A3Q000F2Q0063000A000B4Q000400093Q000B0004423Q006E000100204B0006000600102Q0037000E00043Q002078000F000D00112Q0059000E000E000F000677000E003900013Q0004423Q0039000100204B0007000700100004423Q006800012Q0037000E00054Q0011000F000D4Q0058000E00020002000677000E006700013Q0004423Q00670001002070000E000D0007001232001000124Q003F000E00100002000649000E0049000100010004423Q00490001002070000E000D0007001232001000134Q003F000E00100002000649000E0049000100010004423Q00490001002078000E000D0014000677000E006800013Q0004423Q00680001002078000F000E000B000677000F006800013Q0004423Q00680001002078000F000E000B002078000F000F00150020780010000300152Q0015000F000F00100020780010000E000B0020780010001000160020780011000300162Q00150010001000110020780011000E000B0020780011001100170020780012000300172Q001500110011001200121A001200183Q0020780012001200192Q00520013000F000F2Q00520014001000102Q003E0013001300142Q00520014001100112Q003E0013001300142Q005800120002000200066E00120068000100050004423Q006800012Q0011000500124Q00110004000D3Q0004423Q0068000100204B000800080010002067000E0006001A002682000E006E0001000D0004423Q006E000100121A000E00013Q002078000E000E00022Q0053000E0001000100065A00090031000100020004423Q003100012Q001800095Q00121A000A001B3Q00065E000B3Q000100052Q00713Q00034Q00713Q00064Q00033Q00094Q00713Q00074Q00713Q00084Q0026000A000200010006490009007D000100010004423Q007D00012Q0062000400093Q0004423Q007F00012Q0050000A000A4Q0062000A00094Q00297Q0004425Q00012Q00297Q0004425Q00010004425Q00012Q00073Q00013Q00013Q00093Q0003093Q00506C6179657247756903043Q004D61696E030E3Q0046696E6446697273744368696C6403063Q004F787967656E03083Q00746F6E756D626572030C3Q00476574412Q7472696275746503093Q006F6C646F787967656E026Q005940029Q00224Q00377Q0020785Q00010020785Q00020020705Q0003001232000200044Q003F3Q000200020006773Q002100013Q0004423Q0021000100121A000100053Q00207000023Q0006001232000400074Q006A000200044Q004A00013Q000200064900010010000100010004423Q00100001001232000100084Q0037000200013Q000E1B00090016000100020004423Q001600012Q0037000200013Q00064900020017000100010004423Q00170001001232000200084Q004E00030001000200205D0003000300082Q0037000400034Q0037000500044Q003E00040004000500061200030002000100040004423Q001F00012Q003C00046Q0018000400014Q0062000400024Q00073Q00017Q00053Q00028Q0003043Q007461736B03043Q0077616974029A5Q99A93F03053Q007063612Q6C00253Q0012323Q00013Q00121A000100023Q002078000100010003001232000200044Q00260001000200012Q003700015Q0006770001000900013Q0004423Q000900010004423Q000100012Q0037000100013Q0006770001001500013Q0004423Q001500012Q0037000100023Q0006770001001500013Q0004423Q001500010012323Q00013Q00121A000100053Q00065E00023Q000100012Q00713Q00024Q00260001000200010004423Q000100012Q0037000100013Q0006770001000100013Q0004423Q000100012Q0037000100023Q00064900010001000100010004423Q000100012Q0037000100033Q00064900010001000100010004423Q0001000100121A000100053Q00065E00020001000100022Q00713Q00044Q00038Q00260001000200010004423Q000100012Q00073Q00013Q00023Q00083Q00030E3Q0046696E6446697273744368696C6403043Q004865616403083Q00522Q6F7450617274030B3Q005072696D6172795061727403093Q00776F726B7370616365030D3Q0043752Q72656E7443616D65726103063Q006C2Q6F6B417403083Q00506F736974696F6E00194Q00377Q0020705Q0001001232000200024Q003F3Q000200020006493Q000E000100010004423Q000E00012Q00377Q0020705Q0001001232000200034Q003F3Q000200020006493Q000E000100010004423Q000E00012Q00377Q0020785Q00040006773Q001800013Q0004423Q0018000100121A000100053Q00207800010001000600207800010001000700121A000200053Q00207800020002000600207800020002000800207800033Q00082Q007F0001000300012Q00073Q00017Q00113Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F7450617274026Q00F03F025Q0080764003043Q006D6174682Q033Q00726164026Q00344003083Q00506F736974696F6E03073Q00566563746F72332Q033Q006E65772Q033Q00636F73028Q002Q033Q0073696E03093Q00776F726B7370616365030D3Q0043752Q72656E7443616D65726103063Q006C2Q6F6B4174002C4Q00377Q0020785Q00010006430001000700013Q0004423Q0007000100207000013Q0002001232000300034Q003F0001000300020006490001000A000100010004423Q000A00012Q00073Q00014Q0037000200013Q00204B0002000200040020670002000200052Q0062000200013Q00121A000200063Q0020780002000200072Q0037000300014Q0058000200020002001232000300083Q00207800040001000900121A0005000A3Q00207800050005000B00121A000600063Q00207800060006000C2Q0011000700024Q00580006000200022Q00520006000600030012320007000D3Q00121A000800063Q00207800080008000E2Q0011000900024Q00580008000200022Q00520008000800032Q003F0005000800022Q003E00040004000500121A0005000F3Q00207800050005001000207800050005001100121A0006000F3Q0020780006000600100020780006000600092Q0011000700044Q007F0005000700012Q00073Q00017Q00043Q0003043Q007461736B03043Q0077616974026Q00F03F03053Q007063612Q6C00123Q00121A3Q00013Q0020785Q0002001232000100034Q00263Q000200012Q00377Q0006775Q00013Q0004425Q00012Q00373Q00013Q0006495Q000100010004425Q000100121A3Q00043Q00065E00013Q000100012Q00713Q00024Q00643Q000200010006495Q000100010004425Q00010004425Q00012Q00073Q00013Q00013Q000F3Q0003093Q00506C6179657247756903043Q004D61696E030B3Q004361746368696E6742617203053Q004672616D652Q033Q0042617203053Q00436174636803053Q0047722Q656E03073Q00412Q6472652Q73030C3Q006D656D6F72795F777269746503053Q00666C6F6174025Q00A09440026Q00F03F025Q00B09440025Q00C09440025Q00D0944000214Q00377Q0020785Q00010020785Q00020020785Q00030020785Q00040020785Q000500207800013Q00060020780001000100070020780001000100080006770001002000013Q0004423Q0020000100121A000200093Q0012320003000A3Q00204B00040001000B0012320005000C4Q007F00020005000100121A000200093Q0012320003000A3Q00204B00040001000D0012320005000C4Q007F00020005000100121A000200093Q0012320003000A3Q00204B00040001000E0012320005000C4Q007F00020005000100121A000200093Q0012320003000A3Q00204B00040001000F0012320005000C4Q007F0002000500010004423Q002000012Q00073Q00017Q002E3Q00028Q0003043Q007461736B03043Q0077616974029A5Q99B93F029A5Q99C93F03083Q006B65797072652Q73025Q0040524003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403043Q007761726E03303Q005B4162792Q73616C5D204D61696E206379636C653A2048756D616E6F6964522Q6F7450617274206E6F7420666F756E6403093Q00506C6179657247756903043Q004D61696E03063Q004F787967656E03293Q005B4162792Q73616C5D204D61696E206379636C653A204F787967656E205549206E6F7420666F756E6403083Q00746F6E756D626572030C3Q00476574412Q7472696275746503093Q006F6C646F787967656E026Q005940027Q0040025Q0080584003053Q00737061776E03093Q00776F726B737061636503043Q0047616D6503043Q004669736803063Q00636C69656E74033D3Q005B4162792Q73616C5D204669736820666F6C646572206E6F7420666F756E6420617420776F726B73706163652E47616D652E466973682E636C69656E7403063Q00506172656E7403043Q004E616D65010003083Q00666973685479706503013Q003F030C3Q00666973684D75746174696F6E03083Q00522Q6F745061727403043Q004865616403083Q00506F736974696F6E03013Q005803013Q005903013Q005A03043Q006D61746803043Q0073717274026Q00144003053Q007063612Q6C030B3Q006D6F75736531636C69636B2Q0008012Q001232000100013Q00121A000200023Q002078000200020003001232000300044Q00260002000200012Q003700025Q0006770002000E00013Q0004423Q000E00012Q0037000200013Q0006490002000E000100010004423Q000E00012Q0037000200023Q0006770002001E00013Q0004423Q001E00012Q0037000200023Q0006770002000100013Q0004423Q000100012Q0037000200023Q0006770002001900013Q0004423Q0019000100121A000200023Q002078000200020003001232000300044Q00260002000200010004423Q0011000100121A000200023Q002078000200020003001232000300054Q00260002000200010004423Q0001000100121A000200063Q001232000300074Q00260002000200012Q0037000200033Q00207800020002000800064300030028000100020004423Q002800010020700003000200090012320005000A4Q003F0003000500020006490003002E000100010004423Q002E000100121A0004000B3Q0012320005000C4Q00260004000200010004423Q000100012Q0037000400033Q00207800040004000D00207800040004000E0020700004000400090012320006000F4Q003F00040006000200064900040039000100010004423Q0039000100121A0005000B3Q001232000600104Q00260005000200010006770004004200013Q0004423Q0042000100121A000500113Q002070000600040012001232000800134Q006A000600084Q004A00053Q000200064900050043000100010004423Q00430001001232000500144Q0037000600043Q00066E00060047000100050004423Q004700012Q0062000500044Q0037000600043Q000E1B0001004D000100060004423Q004D00012Q0037000600043Q0006490006004E000100010004423Q004E0001001232000600144Q004E00070005000600205D00070007001400204B000100010004000E5400150054000100010004423Q00540001001232000100013Q0006770004006100013Q0004423Q006100012Q0037000800054Q0037000900064Q003E00080008000900062E00070061000100080004423Q006100012Q0037000800073Q00064900080061000100010004423Q006100012Q0018000800014Q0062000800073Q0004423Q006F0001000E540016006F000100070004423Q006F00012Q0037000800073Q0006770008006F00013Q0004423Q006F00012Q001800086Q0062000800074Q0037000800083Q0006770008006F00013Q0004423Q006F00012Q0018000800014Q0062000800024Q0037000800094Q00530008000100012Q0037000800073Q0006770008007F00013Q0004423Q007F00012Q0050000800084Q00620008000A3Q00121A000800023Q00207800080008001700065E00093Q000100052Q00713Q000B4Q00033Q00034Q00713Q000C4Q00713Q000D4Q00713Q000E4Q00260008000200012Q002900025Q0004423Q0001000100121A000800183Q00207800080008001900207800080008001A00207800080008001B0006490008008A000100010004423Q008A000100121A0009000B3Q001232000A001C4Q00260009000200012Q002900025Q0004423Q000100012Q00370009000A3Q0006770009009D00013Q0004423Q009D0001002078000A0009001D000677000A009D00013Q0004423Q009D0001002070000A00080009002078000C0009001E2Q003F000A000C0002000677000A009D00013Q0004423Q009D00012Q0037000A000F4Q0011000B00094Q0058000A00020002000649000A009D000100010004423Q009D00012Q0050000A000A4Q0062000A000A4Q0050000900093Q000677000900FF00013Q0004423Q00FF0001002078000A0009001D000677000A00FF00013Q0004423Q00FF0001002078000A0009001E0006233Q00B80001000A0004423Q00B800012Q0037000A00104Q0059000A000A0009000677000A00AE00013Q0004423Q00AE0001002680000A00AE0001001F0004423Q00AE0001002078000B000A0020000649000B00AF000100010004423Q00AF0001001232000B00213Q000677000A00B600013Q0004423Q00B60001002680000A00B60001001F0004423Q00B60001002078000C000A0022000649000C00B7000100010004423Q00B70001001232000C00213Q0020783Q0009001E002070000A00090009001232000C000A4Q003F000A000C0002000649000A00C5000100010004423Q00C50001002070000A00090009001232000C00234Q003F000A000C0002000649000A00C5000100010004423Q00C50001002070000A00090009001232000C00244Q003F000A000C0002000677000A00022Q013Q0004423Q00022Q01002078000B000A0025002078000C000B0026002078000D00030025002078000D000D00262Q0015000C000C000D002078000D000B0027002078000E00030025002078000E000E00272Q0015000D000D000E002078000E000B0028002078000F00030025002078000F000F00282Q0015000E000E000F00121A000F00293Q002078000F000F002A2Q00520010000C000C2Q00520011000D000D2Q003E0010001000112Q00520011000E000E2Q003E0010001000112Q0058000F000200022Q0037001000054Q0037001100064Q003E00100010001100061200070002000100100004423Q00E200012Q003C00106Q0018001000014Q0037001100113Q00066E001100F10001000F0004423Q00F10001000649001000F1000100010004423Q00F1000100121A001100023Q00207800110011001700065E00120001000100042Q00713Q000B4Q00033Q00034Q00033Q00094Q00713Q00114Q00260011000200010004423Q00022Q01000649001000022Q0100010004423Q00022Q0100121A001100293Q00207800110011002A2Q00520012000C000C2Q00520013000E000E2Q003E0012001200132Q0058001100020002000E1B002B00022Q0100110004423Q00022Q0100121A0011002C3Q00121A0012002D4Q00260011000200010004423Q00022Q010026803Q00022Q01002E0004423Q00022Q012Q00508Q002900025Q0004423Q000100012Q002900025Q0004423Q000100010004423Q000100012Q00073Q00013Q00023Q00023Q00026Q004E4003083Q00536166655A6F6E65000C4Q00378Q0037000100013Q00065E00023Q000100012Q00713Q00024Q0050000300033Q001232000400014Q0037000500034Q0037000600044Q004E000500050006001232000600024Q007F3Q000600012Q00073Q00013Q00018Q00034Q00378Q00363Q00024Q00073Q00017Q00013Q0003043Q004E616D65000D4Q00378Q0037000100013Q00065E00023Q000100012Q00713Q00023Q00065E00030001000100032Q00713Q00024Q00713Q00034Q00713Q00014Q0050000400054Q0037000600023Q0020780006000600012Q007F3Q000600012Q00073Q00013Q00023Q000C3Q0003063Q00506172656E74030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403083Q00522Q6F745061727403043Q004865616403073Q00566563746F72332Q033Q006E657703083Q00506F736974696F6E03013Q0058026Q00244003013Q005903013Q005A00274Q00377Q0006773Q002400013Q0004423Q002400012Q00377Q0020785Q00010006773Q002400013Q0004423Q002400012Q00377Q0020705Q0002001232000200034Q003F3Q000200020006493Q0017000100010004423Q001700012Q00377Q0020705Q0002001232000200044Q003F3Q000200020006493Q0017000100010004423Q001700012Q00377Q0020705Q0002001232000200054Q003F3Q000200020006773Q002400013Q0004423Q0024000100121A000100063Q00207800010001000700207800023Q000800207800020002000900204B00020002000A00207800033Q000800207800030003000B00207800043Q000800207800040004000C2Q0009000100044Q000B00016Q00508Q00363Q00024Q00073Q00017Q00093Q00030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403083Q00522Q6F745061727403043Q004865616403043Q006D6174682Q033Q0061627303083Q00506F736974696F6E03013Q0059026Q002040012D4Q003700015Q0006770001001300013Q0004423Q001300012Q003700015Q002070000100010001001232000300024Q003F00010003000200064900010013000100010004423Q001300012Q003700015Q002070000100010001001232000300034Q003F00010003000200064900010013000100010004423Q001300012Q003700015Q002070000100010001001232000300044Q003F0001000300020006770001002600013Q0004423Q002600012Q0037000200013Q00062E3Q0023000100020004423Q0023000100121A000200053Q0020780002000200062Q0037000300023Q0020780003000300070020780003000300080020780004000100070020780004000400082Q00150003000300042Q005800020002000200266B00020024000100090004423Q002400012Q003C00026Q0018000200014Q0036000200024Q0037000200013Q0006123Q0002000100020004423Q002A00012Q003C00026Q0018000200014Q0036000200024Q00073Q00017Q00", GetFEnv(), ...);