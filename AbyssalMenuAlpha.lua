-- @ptacunit
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
				if (Enum <= 66) then
					if (Enum <= 32) then
						if (Enum <= 15) then
							if (Enum <= 7) then
								if (Enum <= 3) then
									if (Enum <= 1) then
										if (Enum == 0) then
											if (Stk[Inst[2]] < Stk[Inst[4]]) then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										else
											Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										end
									elseif (Enum == 2) then
										Stk[Inst[2]] = Env[Inst[3]];
									elseif (Inst[2] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum <= 5) then
									if (Enum > 4) then
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
								elseif (Enum > 6) then
									Stk[Inst[2]] = Stk[Inst[3]];
								else
									local A = Inst[2];
									local B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								end
							elseif (Enum <= 11) then
								if (Enum <= 9) then
									if (Enum == 8) then
										local A = Inst[2];
										local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
										local Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
									else
										local A = Inst[2];
										local T = Stk[A];
										local B = Inst[3];
										for Idx = 1, B do
											T[Idx] = Stk[A + Idx];
										end
									end
								elseif (Enum == 10) then
									Stk[Inst[2]] = not Stk[Inst[3]];
								else
									local A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
								end
							elseif (Enum <= 13) then
								if (Enum > 12) then
									if (Stk[Inst[2]] == Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
								end
							elseif (Enum > 14) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								Upvalues[Inst[3]] = Stk[Inst[2]];
							end
						elseif (Enum <= 23) then
							if (Enum <= 19) then
								if (Enum <= 17) then
									if (Enum == 16) then
										Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
									elseif (Stk[Inst[2]] > Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 18) then
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
									Stk[Inst[2]] = #Stk[Inst[3]];
								end
							elseif (Enum <= 21) then
								if (Enum == 20) then
									VIP = Inst[3];
								else
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
										if (Mvm[1] == 61) then
											Indexes[Idx - 1] = {Stk,Mvm[3]};
										else
											Indexes[Idx - 1] = {Upvalues,Mvm[3]};
										end
										Lupvals[#Lupvals + 1] = Indexes;
									end
									Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
								end
							elseif (Enum > 22) then
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							else
								local B = Stk[Inst[4]];
								if not B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 27) then
							if (Enum <= 25) then
								if (Enum == 24) then
									if (Stk[Inst[2]] <= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = #Stk[Inst[3]];
								end
							elseif (Enum > 26) then
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum <= 29) then
							if (Enum == 28) then
								Stk[Inst[2]] = {};
							elseif (Stk[Inst[2]] ~= Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 30) then
							local A = Inst[2];
							Stk[A] = Stk[A]();
						elseif (Enum == 31) then
							if (Stk[Inst[2]] < Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						end
					elseif (Enum <= 49) then
						if (Enum <= 40) then
							if (Enum <= 36) then
								if (Enum <= 34) then
									if (Enum > 33) then
										Stk[Inst[2]] = Inst[3] / Stk[Inst[4]];
									else
										Stk[Inst[2]][Inst[3]] = Inst[4];
									end
								elseif (Enum > 35) then
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
									Stk[Inst[2]] = {};
								end
							elseif (Enum <= 38) then
								if (Enum > 37) then
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								else
									VIP = Inst[3];
								end
							elseif (Enum > 39) then
								Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum <= 44) then
							if (Enum <= 42) then
								if (Enum == 41) then
									Stk[Inst[2]] = Inst[3] ~= 0;
								else
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								end
							elseif (Enum == 43) then
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
								Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
							end
						elseif (Enum <= 46) then
							if (Enum > 45) then
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							elseif (Stk[Inst[2]] > Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 47) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						elseif (Enum == 48) then
							Stk[Inst[2]] = Inst[3] ~= 0;
						else
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						end
					elseif (Enum <= 57) then
						if (Enum <= 53) then
							if (Enum <= 51) then
								if (Enum == 50) then
									if (Stk[Inst[2]] == Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								end
							elseif (Enum == 52) then
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
							elseif not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 55) then
							if (Enum > 54) then
								do
									return Stk[Inst[2]];
								end
							else
								do
									return;
								end
							end
						elseif (Enum == 56) then
							local A = Inst[2];
							Stk[A] = Stk[A]();
						elseif (Inst[2] < Stk[Inst[4]]) then
							VIP = Inst[3];
						else
							VIP = VIP + 1;
						end
					elseif (Enum <= 61) then
						if (Enum <= 59) then
							if (Enum == 58) then
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							elseif Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 60) then
							Stk[Inst[2]] = Stk[Inst[3]];
						else
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
						end
					elseif (Enum <= 63) then
						if (Enum > 62) then
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 64) then
						local A = Inst[2];
						do
							return Unpack(Stk, A, Top);
						end
					elseif (Enum > 65) then
						Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
					else
						Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
					end
				elseif (Enum <= 99) then
					if (Enum <= 82) then
						if (Enum <= 74) then
							if (Enum <= 70) then
								if (Enum <= 68) then
									if (Enum > 67) then
										Stk[Inst[2]]();
									else
										local A = Inst[2];
										local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
										local Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
									end
								elseif (Enum == 69) then
									local B = Inst[3];
									local K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
								elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 72) then
								if (Enum > 71) then
									local A = Inst[2];
									Stk[A](Stk[A + 1]);
								else
									local B = Stk[Inst[4]];
									if not B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								end
							elseif (Enum == 73) then
								Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
							else
								local A = Inst[2];
								local T = Stk[A];
								local B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							end
						elseif (Enum <= 78) then
							if (Enum <= 76) then
								if (Enum == 75) then
									local A = Inst[2];
									do
										return Unpack(Stk, A, A + Inst[3]);
									end
								elseif (Stk[Inst[2]] ~= Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 77) then
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								local T = Stk[A];
								for Idx = A + 1, Inst[3] do
									Insert(T, Stk[Idx]);
								end
							end
						elseif (Enum <= 80) then
							if (Enum == 79) then
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
							else
								Stk[Inst[2]][Inst[3]] = Inst[4];
							end
						elseif (Enum > 81) then
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						else
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						end
					elseif (Enum <= 90) then
						if (Enum <= 86) then
							if (Enum <= 84) then
								if (Enum == 83) then
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = Env[Inst[3]];
								end
							elseif (Enum > 85) then
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
							elseif (Inst[2] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 88) then
							if (Enum > 87) then
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							else
								local B = Stk[Inst[4]];
								if B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							end
						elseif (Enum > 89) then
							local A = Inst[2];
							local Results = {Stk[A](Stk[A + 1])};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							local A = Inst[2];
							Stk[A](Stk[A + 1]);
						end
					elseif (Enum <= 94) then
						if (Enum <= 92) then
							if (Enum > 91) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							elseif (Inst[2] < Stk[Inst[4]]) then
								VIP = Inst[3];
							else
								VIP = VIP + 1;
							end
						elseif (Enum == 93) then
							if (Stk[Inst[2]] > Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = VIP + Inst[3];
							end
						else
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 96) then
						if (Enum == 95) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						else
							Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
						end
					elseif (Enum <= 97) then
						do
							return Stk[Inst[2]];
						end
					elseif (Enum == 98) then
						do
							return;
						end
					else
						local B = Inst[3];
						local K = Stk[B];
						for Idx = B + 1, Inst[4] do
							K = K .. Stk[Idx];
						end
						Stk[Inst[2]] = K;
					end
				elseif (Enum <= 116) then
					if (Enum <= 107) then
						if (Enum <= 103) then
							if (Enum <= 101) then
								if (Enum > 100) then
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
										if (Mvm[1] == 61) then
											Indexes[Idx - 1] = {Stk,Mvm[3]};
										else
											Indexes[Idx - 1] = {Upvalues,Mvm[3]};
										end
										Lupvals[#Lupvals + 1] = Indexes;
									end
									Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
								end
							elseif (Enum > 102) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							else
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 105) then
							if (Enum > 104) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
							elseif (Stk[Inst[2]] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 106) then
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 111) then
						if (Enum <= 109) then
							if (Enum > 108) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
							end
						elseif (Enum == 110) then
							local B = Stk[Inst[4]];
							if B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						else
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
						end
					elseif (Enum <= 113) then
						if (Enum == 112) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						elseif (Stk[Inst[2]] > Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = VIP + Inst[3];
						end
					elseif (Enum <= 114) then
						if (Stk[Inst[2]] < Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum > 115) then
						Stk[Inst[2]]();
					else
						Stk[Inst[2]] = Inst[3];
					end
				elseif (Enum <= 124) then
					if (Enum <= 120) then
						if (Enum <= 118) then
							if (Enum == 117) then
								Upvalues[Inst[3]] = Stk[Inst[2]];
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
							end
						elseif (Enum > 119) then
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
						end
					elseif (Enum <= 122) then
						if (Enum > 121) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						else
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum > 123) then
						Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
					else
						Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
					end
				elseif (Enum <= 128) then
					if (Enum <= 126) then
						if (Enum == 125) then
							if (Inst[2] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum == 127) then
						local A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
					elseif Stk[Inst[2]] then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 130) then
					if (Enum > 129) then
						Stk[Inst[2]] = not Stk[Inst[3]];
					else
						Stk[Inst[2]] = Inst[3] / Stk[Inst[4]];
					end
				elseif (Enum <= 131) then
					local A = Inst[2];
					local B = Stk[Inst[3]];
					Stk[A + 1] = B;
					Stk[A] = B[Inst[4]];
				elseif (Enum > 132) then
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
				elseif (Inst[2] < Stk[Inst[4]]) then
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
return VMCall("LOL!FE3Q0003043Q0067616D65030A3Q004765745365727669636503073Q00506C6179657273030B3Q004C6F63616C506C6179657203103Q0055736572496E7075745365727669636503053Q007072696E74031C3Q005B4162792Q73616C5D20536372697074207374617274696E673Q2E030E3Q00466F72676F2Q74656E20442Q657003073Q00566563746F72332Q033Q006E6577021F85EB51B8FE57C002F853E3A51B10B3402Q022B8716D90E27C0030D3Q00416E6369656E742053616E6473024Q33B3E09BC002B81E85EB912DB14002FCA9F1D24DA22F40030C3Q0053756E6B656E2057696C647302736891ED7C40ADC0024Q33731DA340026891ED7CFFB2B3C0030C3Q0053706972697420522Q6F74730248E17A14AEFE994002378941602583AF4002F6285C8FC2E59DC0031D3Q005B4162792Q73616C5D2044656661756C74206661726D20617265613A20028Q00026Q005440026Q000840027Q0040026Q003940026Q003E40031E3Q005B4162792Q73616C5D2053652Q74696E677320696E697469616C697A656403223Q005B4162792Q73616C5D3Q206F78795468726573686F6C6450657263656E74203D20031C3Q005B4162792Q73616C5D3Q2074772Q656E4475726174696F6E203D2003163Q005B4162792Q73616C5D3Q206D696E44697374203D2003193Q005B4162792Q73616C5D2048656C7065727320646566696E656403213Q005B4162792Q73616C5D204D6F76656D656E7420656E67696E6520646566696E6564031F3Q005B4162792Q73616C5D204C6F6164696E67205549206C6962726172793Q2E030A3Q006C6F6164737472696E6703073Q00482Q747047657403443Q00682Q7470733A2Q2F7261772E67697468756275736572636F6E74656E742E636F6D2F7A2Q652D373635342F55492F726566732F68656164732F6D61696E2F55492E6C756103223Q005B4162792Q73616C5D205549206C696272617279206C6F616465642C205549203D2003083Q00746F737472696E6703023Q00554903063Q006E6F74696679030C3Q004162792Q73616C204D656E7503093Q005549204C6F61646564026Q00244003063Q0057696E646F7703053Q005469746C6503243Q004162792Q73616C204D656E75207C204275696C643A20416C706861207C204D617463686103043Q0053697A6503073Q00566563746F7232025Q00407F40025Q00E0754003043Q004F70656E2Q0103053Q005468656D6503063Q00476C6F62616C030B3Q004C69676874412Q63656E7403063Q00436F6C6F723303073Q0066726F6D524742026Q005940026Q006940025Q00E06F4003063Q00412Q63656E74026Q004940026Q005E40025Q00806B40030A3Q004461726B412Q63656E74025Q00805140025Q00C0624003093Q004C6967687442617365026Q002E40026Q003440025Q0080464003043Q0042617365026Q00284003083Q004461726B42617365026Q001440026Q00184003043Q0054657874026Q006E4003083Q00436F2Q6C61707365026Q00644003063Q00436F726E657203073Q0050612Q64696E6703173Q005B4162792Q73616C5D205468656D6520612Q706C69656403183Q005B4162792Q73616C5D2057696E646F7720637265617465642Q033Q0054616203043Q00486F6D6503073Q0053656374696F6E03043Q00496E666F03053Q004C6162656C03253Q0048652Q6C6F2C207468616E6B20796F7520666F72207573696E67206D79207363726970742E03173Q004D616465206279204070746163756E6974202F2066616C03303Q00646D204070746163756E697420666F7220616E7920692Q73756573202F2062756773202F2073752Q67657374696F6E7303083Q00496E7465726E616C03093Q00436F2Q6C617073656403113Q00506572666F726D616E636520537461747303063Q004D656D6F7279030A3Q004D656D6F72793A202Q2D2Q033Q0043505503073Q004350553A202Q2D2Q033Q0047505503073Q004750553A202Q2D031A3Q005B4162792Q73616C5D20486F6D6520746162206372656174656403043Q007461736B03053Q00737061776E03073Q004661726D696E6703093Q004175746F204661726D03253Q005B4162792Q73616C5D204661726D696E67207461622F73656374696F6E206372656174656403083Q00436865636B626F7803063Q00456E61626C6503073Q0044656661756C74010003073Q004B657962696E64030F3Q00546F2Q676C65204175746F6661726D2Q033Q004B657903043Q00456E756D03073Q004B6579436F646503013Q005003053Q00706169727303053Q007461626C6503063Q00696E73657274031C3Q005B4162792Q73616C5D204C6F636174696F6E2063686F696365733A2003063Q00636F6E63617403023Q002C2003083Q0044726F70646F776E03093Q004661726D204172656103073Q004F7074696F6E7303063Q00536C6964657203103Q004F787967656E205468726573686F6C642Q033Q004D696E2Q033Q004D617803043Q005374657003063Q0053752Q66697803013Q002503273Q005B4162792Q73616C5D204661726D696E672073656374696F6E207769646765747320612Q64656403053Q00437570696403063Q004C6F6E656C7903053Q005368696E7903043Q00502Q6F7003043Q00526F636B03053Q00436F72616C03043Q004D6F2Q7303053Q004D6574616C03043Q0053616E6403063Q00416C62696E6F030B3Q005472616E73706172656E7403063Q0043616374757303063Q0053706972697403063Q00466F2Q73696C03063Q00476F6C64656E03083Q004E6567617469766503053Q00466169727903093Q00496E76697369626C6503043Q004E656F6E030B3Q00556C74726176696F6C657403063Q00522Q6F74656403063Q00536861646F7703073Q00416E67656C696303073Q004162792Q73616C03083Q0047726F756E64656403063Q0042616E616E6103043Q004A61646503063Q004C6971756964030D3Q00416E6369656E7420536861726B030A3Q00416E676C65726669736803093Q0042612Q726163756461030C3Q004269676D6F75746866697368030D3Q00426C61636B66696E2054756E6103083Q00426C6F626669736803093Q00426C75652054616E67030C3Q00426C756566696E2054756E6103083Q00436176656669736803093Q00436C6F776E666973682Q033Q00436F6403063Q00446973637573030A3Q00447261676F6E6669736803073Q004579656669736803073Q0047726F75706572030C3Q0048612Q6D657220536861726B03133Q00496E666C617465642050752Q66657266697368030C3Q004A616775617220536861726B03093Q004A652Q6C7966697368030F3Q004B696E6720416E676C65726669736803083Q004C696F6E6669736803093Q004D616869204D616869030A3Q004D6F736173617572757303083Q004E61706F6C656F6E03073Q004E61727768616C030F3Q00506163696669632046616E66697368030B3Q0050656C6963616E2045656C03073Q00506972616E686103073Q00506F6D70616E6F030A3Q0050752Q66657266697368030D3Q005361636162616D62617370697303083Q005361696C6669736803063Q0053616C6D6F6E030C3Q0053636F7270696F6E6669736803093Q0053656120486F727365030A3Q0053656120547572746C6503053Q00536861726B03053Q00537175696403073Q0053756E6669736803083Q0054616D626171756903043Q0054616E67030B3Q00546F7563616E204669736803053Q0054726F757403053Q005768616C65030B3Q00466973682046696C74657203283Q0053656C656374206D75746174696F6E7320746F207461726765742028656D707479203D20612Q6C29030D3Q004D756C746944726F70646F776E03093Q004D75746174696F6E7303293Q0053656C656374206669736820747970657320746F207461726765742028656D707479203D20612Q6C29030C3Q00466973682054797065732031030C3Q00466973682054797065732032030D3Q0052657365742046696C7465727303063Q0042752Q746F6E03233Q005B4162792Q73616C5D20466973682066696C7465722073656374696F6E20612Q646564032C3Q004661726D2053652Q74696E6773205B44616E6765726F75732C204564697420776974682043617574696F6E5D032D3Q0074772Q656E4475726174696F6E202D205365636F6E647320746F20436F6D706C65746520416E696D6174696F6E030E3Q0054772Q656E204475726174696F6E026Q00F03F026Q00E03F03013Q007303153Q00526573657420746F2044656661756C74202833732903313Q007265747265617453702Q65644D756C7469706C696572202D204D756C7469706C69657320526574726561742053702Q656403133Q00526574726561742053702Q6564204D756C746903013Q007803153Q00526573657420746F2044656661756C74202832782903203Q006D696E44697374202D20466973682053682Q6F74696E672044697374616E6365030C3Q004D696E2044697374616E636503063Q00207374756473031B3Q00526573657420746F2044656661756C74202832352073747564732903233Q0074772Q656E5374657073202D20506F736974696F6E2055706461746520416D6F756E74030B3Q0054772Q656E20537465707303153Q00526573657420746F2044656661756C74202833302903283Q005B4162792Q73616C5D20416476616E6365642073656374696F6E207769646765747320612Q64656403083Q0054656C65706F727403093Q004C6F636174696F6E7303263Q005B4162792Q73616C5D2054656C65706F7274207461622F73656374696F6E206372656174656403213Q005B4162792Q73616C5D20412Q6465642074656C65706F72742062752Q746F6E3A2003043Q004D69736303093Q005574696C697469657303213Q00546869732069732061206E6F636C697020616E7469636865617420627970612Q7303223Q00596F752077692Q6C206861766520746F2072656A6F696E20746F2064697361626C6503283Q005468657265666F726520796F752063612Q6E6F7420746F756368206C616E64206E6F722073652Q6C030E3Q00456E61626C65204E6F2D636C6970031A3Q005B4162792Q73616C5D204D69736320746162206372656174656403193Q005B4162792Q73616C5D2055492066752Q6C79206C6F61646564031E3Q005B4162792Q73616C5D20412Q6C2073797374656D73206C61756E6368656400E7022Q0012543Q00013Q0020835Q000200121A000200034Q005C3Q0002000200205100013Q0004001254000200013Q00208300020002000200121A000400054Q005C000200040002001254000300063Q00121A000400074Q00590003000200012Q001C00033Q0004001254000400093Q00205100040004000A00121A0005000B3Q00121A0006000C3Q00121A0007000D4Q005C00040007000200102A000300080004001254000400093Q00205100040004000A00121A0005000F3Q00121A000600103Q00121A000700114Q005C00040007000200102A0003000E0004001254000400093Q00205100040004000A00121A000500133Q00121A000600143Q00121A000700154Q005C00040007000200102A000300120004001254000400093Q00205100040004000A00121A000500173Q00121A000600183Q00121A000700194Q005C00040007000200102A00030016000400121A000400084Q0017000500030004001254000600063Q00121A0007001A4Q0007000800044Q00630007000700082Q00590006000200012Q003000065Q00121A0007001B3Q00121A0008001C4Q003000096Q0030000A6Q004F000B000B4Q001C000C5Q00121A000D001D3Q00121A000E001E3Q00121A000F001F3Q00121A001000204Q007B0011000D00102Q001C00126Q001C00136Q001C00146Q001C00155Q001254001600063Q00121A001700214Q0059001600020001001254001600063Q00121A001700224Q0007001800084Q00630017001700182Q0059001600020001001254001600063Q00121A001700234Q00070018000D4Q00630017001700182Q0059001600020001001254001600063Q00121A001700244Q00070018000F4Q00630017001700182Q005900160002000100066400163Q000100022Q003D3Q00124Q003D3Q00133Q00022C001700013Q00066400180002000100012Q003D3Q00013Q001254001900063Q00121A001A00254Q005900190002000100066400190003000100082Q003D3Q000A4Q003D3Q00014Q003D3Q00104Q003D3Q00114Q003D3Q00174Q003D3Q00064Q003D3Q000C4Q003D3Q00183Q000664001A0004000100032Q003D3Q00014Q003D3Q00174Q003D3Q00183Q001254001B00063Q00121A001C00264Q0059001B00020001001254001B00063Q00121A001C00274Q0059001B00020001001254001B00283Q001254001C00013Q002083001C001C002900121A001E002A4Q006D001C001E4Q0027001B3Q00022Q0074001B00010001001254001B00063Q00121A001C002B3Q001254001D002C3Q001254001E002D4Q000B001D000200022Q0063001C001C001D2Q0059001B00020001001254001B002E3Q00121A001C002F3Q00121A001D00303Q00121A001E00314Q002F001B001E0001001254001B002D3Q002083001B001B00322Q001C001D3Q0003003021001D00330034001254001E00363Q002051001E001E000A00121A001F00373Q00121A002000384Q005C001E0020000200102A001D0035001E003021001D0039003A2Q005C001B001D0002002051001C001B003B002051001C001C003C001254001D003E3Q002051001D001D003F00121A001E00403Q00121A001F00413Q00121A002000424Q005C001D0020000200102A001C003D001D002051001C001B003B002051001C001C003C001254001D003E3Q002051001D001D003F00121A001E00443Q00121A001F00453Q00121A002000464Q005C001D0020000200102A001C0043001D002051001C001B003B002051001C001C003C001254001D003E3Q002051001D001D003F00121A001E00203Q00121A001F00483Q00121A002000494Q005C001D0020000200102A001C0047001D002051001C001B003B002051001C001C003C001254001D003E3Q002051001D001D003F00121A001E004B3Q00121A001F004C3Q00121A0020004D4Q005C001D0020000200102A001C004A001D002051001C001B003B002051001C001C003C001254001D003E3Q002051001D001D003F00121A001E00313Q00121A001F004F3Q00121A002000204Q005C001D0020000200102A001C004E001D002051001C001B003B002051001C001C003C001254001D003E3Q002051001D001D003F00121A001E00513Q00121A001F00523Q00121A0020004C4Q005C001D0020000200102A001C0050001D002051001C001B003B002051001C001C003C001254001D003E3Q002051001D001D003F00121A001E00463Q00121A001F00543Q00121A002000424Q005C001D0020000200102A001C0053001D002051001C001B003B002051001C001C003C001254001D003E3Q002051001D001D003F00121A001E00563Q00121A001F00413Q00121A002000424Q005C001D0020000200102A001C0055001D002051001C001B003B002051001C001C003C003021001C00570051002051001C001B003B002051001C001C003C003021001C00580052001254001C00063Q00121A001D00594Q0059001C00020001001254001C00063Q00121A001D005A4Q0059001C00020001002083001C001B005B2Q001C001E3Q0001003021001E0033005C2Q005C001C001E0002002083001D001C005D2Q001C001F3Q0001003021001F0033005E2Q005C001D001F0002002083001E001D005F2Q001C00203Q00010030210020003300602Q002F001E00200001002083001E001D005F2Q001C00203Q00010030210020003300612Q002F001E00200001002083001E001D005F2Q001C00203Q00010030210020003300622Q002F001E00200001002051001E001D0063003021001E0064003A002083001E001C005D2Q001C00203Q00010030210020003300652Q005C001E00200002002051001F001E0063003021001F0064003A2Q001C001F3Q00030020830020001E005F2Q001C00223Q00010030210022003300672Q005C00200022000200102A001F006600200020830020001E005F2Q001C00223Q00010030210022003300692Q005C00200022000200102A001F006800200020830020001E005F2Q001C00223Q000100302100220033006B2Q005C00200022000200102A001F006A0020001254002000063Q00121A0021006C4Q00590020000200010012540020006D3Q00205100200020006E00066400210005000100022Q003D3Q001B4Q003D3Q001F4Q00590020000200010020830020001B005B2Q001C00223Q000100302100220033006F2Q005C00200022000200208300210020005D2Q001C00233Q00010030210023003300702Q005C002100230002001254002200063Q00121A002300714Q00590022000200010020830022002100722Q001C00243Q000200302100240033007300302100240074007500066400250006000100062Q003D3Q00064Q003D3Q00184Q003D3Q00174Q003D3Q00014Q003D3Q000A4Q003D3Q000B4Q002F0022002500010020830022002100762Q001C00243Q0002003021002400330077001254002500793Q00205100250025007A00205100250025007B00102A00240078002500066400250007000100062Q003D3Q00064Q003D3Q00184Q003D3Q00174Q003D3Q00014Q003D3Q000A4Q003D3Q000B3Q00022C002600084Q002F0022002600012Q001C00225Q0012540023007C4Q0007002400034Q005A0023000200250004143Q00472Q010012540028007D3Q00205100280028007E2Q0007002900224Q0007002A00264Q002F0028002A000100062B002300422Q0100020004143Q00422Q01001254002300063Q00121A0024007F3Q0012540025007D3Q0020510025002500802Q0007002600223Q00121A002700814Q005C0025002700022Q00630024002400252Q00590023000200010020830023002100822Q001C00253Q000300302100250033008300102A00250084002200102A00250074000400066400260009000100032Q003D3Q00044Q003D3Q00054Q003D3Q00034Q002F0023002600010020830023002100852Q001C00253Q000600302100250033008600302100250087003100302100250088004000302100250089005100102A0025007400080030210025008A008B0006640026000A000100012Q003D3Q00084Q002F002300260001001254002300063Q00121A0024008C4Q00590023000200012Q001C002300163Q00121A0024008D3Q00121A0025008E3Q00121A0026008F3Q00121A002700903Q00121A002800913Q00121A002900923Q00121A002A00933Q00121A002B00943Q00121A002C00953Q00121A002D00963Q00121A002E00973Q00121A002F00983Q00121A003000993Q00121A0031009A3Q00121A0032009B3Q00121A0033009C3Q00121A0034009D3Q00121A0035009E3Q00121A0036009F3Q00121A003700A03Q00121A003800A13Q00121A003900A23Q00121A003A00A33Q00121A003B00A43Q00121A003C00A53Q00121A003D00A63Q00121A003E00A73Q00121A003F00A84Q004A0023001C00012Q001C0024001B3Q00121A002500A93Q00121A002600AA3Q00121A002700AB3Q00121A002800AC3Q00121A002900AD3Q00121A002A00AE3Q00121A002B00AF3Q00121A002C00B03Q00121A002D00B13Q00121A002E00B23Q00121A002F00B33Q00121A003000B43Q00121A003100B53Q00121A003200B63Q00121A003300B73Q00121A003400B83Q00121A003500B93Q00121A003600BA3Q00121A003700BB3Q00121A003800BC3Q00121A003900BD3Q00121A003A00BE3Q00121A003B00BF3Q00121A003C00C03Q00121A003D00C13Q00121A003E00C23Q00121A003F00C33Q00121A004000C43Q00121A004100C53Q00121A004200C63Q00121A004300C73Q00121A004400C83Q00121A004500C93Q00121A004600CA3Q00121A004700CB3Q00121A004800CC3Q00121A004900CD3Q00121A004A00CE3Q00121A004B00CF3Q00121A004C00D03Q00121A004D00D13Q00121A004E00D23Q00121A004F00D33Q00121A005000D44Q004A0024002C00012Q004F002500273Q00208300280020005D2Q001C002A3Q0001003021002A003300D52Q005C0028002A000200208300290028005F2Q001C002B3Q0001003021002B003300D62Q002F0029002B00010020830029002800D72Q001C002B3Q0003003021002B003300D800102A002B008400232Q001C002C5Q00102A002B0074002C000664002C000B000100012Q003D3Q00124Q005C0029002C00022Q0007002500293Q00208300290028005F2Q001C002B3Q0001003021002B003300D92Q002F0029002B00010020830029002800D72Q001C002B3Q0003003021002B003300DA2Q001C002C00133Q00121A002D00A93Q00121A002E00AA3Q00121A002F00AB3Q00121A003000AC3Q00121A003100AD3Q00121A003200AE3Q00121A003300AF3Q00121A003400B03Q00121A003500B13Q00121A003600B23Q00121A003700B33Q00121A003800B43Q00121A003900B53Q00121A003A00B63Q00121A003B00B73Q00121A003C00B83Q00121A003D00B93Q00121A003E00BA3Q00121A003F00BB3Q00121A004000BC3Q00121A004100BD3Q00121A004200BE4Q004A002C0016000100102A002B0084002C2Q001C002C5Q00102A002B0074002C000664002C000C000100032Q003D3Q00144Q003D3Q00154Q003D3Q00134Q005C0029002C00022Q0007002600293Q0020830029002800D72Q001C002B3Q0003003021002B003300DB2Q001C002C00133Q00121A002D00BF3Q00121A002E00C03Q00121A002F00C13Q00121A003000C23Q00121A003100C33Q00121A003200C43Q00121A003300C53Q00121A003400C63Q00121A003500C73Q00121A003600C83Q00121A003700C93Q00121A003800CA3Q00121A003900CB3Q00121A003A00CC3Q00121A003B00CD3Q00121A003C00CE3Q00121A003D00CF3Q00121A003E00D03Q00121A003F00D13Q00121A004000D23Q00121A004100D33Q00121A004200D44Q004A002C0016000100102A002B0084002C2Q001C002C5Q00102A002B0074002C000664002C000D000100032Q003D3Q00154Q003D3Q00144Q003D3Q00134Q005C0029002C00022Q0007002700293Q00208300290028005F2Q001C002B3Q0001003021002B003300DC2Q002F0029002B00010020830029002800DD2Q001C002B3Q0001003021002B003300DC000664002C000E000100072Q003D3Q00124Q003D3Q00144Q003D3Q00154Q003D3Q00134Q003D3Q00254Q003D3Q00264Q003D3Q00274Q002F0029002C0001001254002900063Q00121A002A00DE4Q005900290002000100208300290020005D2Q001C002B3Q0001003021002B003300DF2Q005C0029002B0002002083002A0029005F2Q001C002C3Q0001003021002C003300E02Q002F002A002C0001002083002A002900852Q001C002C3Q0006003021002C003300E1003021002C008700E2003021002C00880031003021002C008900E3003021002C0074001D003021002C008A00E4000664002D000F000100032Q003D3Q000D4Q003D3Q00114Q003D3Q00104Q005C002A002D0002002083002B002900DD2Q001C002D3Q0001003021002D003300E5000664002E0010000100012Q003D3Q002A4Q002F002B002E0001002083002B0029005F2Q001C002D3Q0001003021002D003300E62Q002F002B002D0001002083002B002900852Q001C002D3Q0006003021002D003300E7003021002D008700E2003021002D00880051003021002D008900E3003021002D0074001E003021002D008A00E8000664002E0011000100012Q003D3Q000E4Q005C002B002E0002002083002C002900DD2Q001C002E3Q0001003021002E003300E9000664002F0012000100012Q003D3Q002B4Q002F002C002F0001002083002C0029005F2Q001C002E3Q0001003021002E003300EA2Q002F002C002E0001002083002C002900852Q001C002E3Q0006003021002E003300EB003021002E00870051003021002E00880040003021002E00890051003021002E0074001F003021002E008A00EC000664002F0013000100012Q003D3Q000F4Q005C002C002F0002002083002D002900DD2Q001C002F3Q0001003021002F003300ED00066400300014000100012Q003D3Q002C4Q002F002D00300001002083002D0029005F2Q001C002F3Q0001003021002F003300EE2Q002F002D002F0001002083002D002900852Q001C002F3Q0005003021002F003300EF003021002F00870031003021002F00880040003021002F00890051003021002F0074002000066400300015000100032Q003D3Q00104Q003D3Q00114Q003D3Q000D4Q005C002D00300002002083002E002900DD2Q001C00303Q00010030210030003300F000066400310016000100012Q003D3Q002D4Q002F002E00310001001254002E00063Q00121A002F00F14Q0059002E00020001002083002E001B005B2Q001C00303Q00010030210030003300F22Q005C002E00300002002083002F002E005D2Q001C00313Q00010030210031003300F32Q005C002F00310002001254003000063Q00121A003100F44Q00590030000200010012540030007C4Q0007003100034Q005A0030000200320004143Q00A302010020830035002F00DD2Q001C00373Q000100102A00370033003300066400380017000100032Q003D3Q00334Q003D3Q001A4Q003D3Q00344Q002F003500380001001254003500063Q00121A003600F54Q0007003700334Q00630036003600372Q00590035000200012Q001300335Q00062B00300095020100020004143Q009502010020830030001B005B2Q001C00323Q00010030210032003300F62Q005C00300032000200208300310030005D2Q001C00333Q00010030210033003300F72Q005C00310033000200208300320031005F2Q001C00343Q00010030210034003300F82Q002F00320034000100208300320031005F2Q001C00343Q00010030210034003300F92Q002F00320034000100208300320031005F2Q001C00343Q00010030210034003300FA2Q002F0032003400010020830032003100DD2Q001C00343Q00010030210034003300FB00066400350018000100012Q003D3Q00014Q002F003200350001001254003200063Q00121A003300FC4Q0059003200020001001254003200063Q00121A003300FD4Q00590032000200010012540032006D3Q00205100320032006E00066400330019000100022Q003D3Q00064Q003D3Q000B4Q00590032000200010012540032006D3Q00205100320032006E0006640033001A000100022Q003D3Q00064Q003D3Q00014Q00590032000200010012540032006D3Q00205100320032006E0006640033001B0001000E2Q003D3Q00064Q003D3Q000A4Q003D3Q00014Q003D3Q00074Q003D3Q00084Q003D3Q00094Q003D3Q000B4Q003D3Q00194Q003D3Q00054Q003D3Q00114Q003D3Q000E4Q003D3Q000C4Q003D3Q00164Q003D3Q000F4Q0059003200020001001254003200063Q00121A003300FE4Q00590032000200012Q00623Q00013Q001C3Q00033Q00028Q0003053Q007063612Q6C03063Q00697061697273013C4Q006900016Q0012000100013Q000E5B00010005000100010004143Q000500012Q003C00016Q0030000100014Q0069000200014Q0012000200023Q000E5B0001000B000100020004143Q000B00012Q003C00026Q0030000200013Q00063500010012000100010004143Q0012000100063500020012000100010004143Q001200012Q0030000300014Q0061000300024Q004F000300043Q001254000500023Q00066400063Q000100032Q003D3Q00034Q003D8Q003D3Q00044Q000B0005000200020006350005001D000100010004143Q001D00012Q003000066Q0061000600024Q000A000600014Q000A000700023Q0006800001002B00013Q0004143Q002B0001001254000800034Q006900096Q005A00080002000A0004143Q0029000100060D000C0029000100040004143Q002900012Q0030000600013Q0004143Q002B000100062B00080025000100020004143Q002500010006800002003700013Q0004143Q00370001001254000800034Q0069000900014Q005A00080002000A0004143Q0035000100060D000C0035000100030004143Q003500012Q0030000700013Q0004143Q0037000100062B00080031000100020004143Q0031000100066E0008003A000100060004143Q003A00012Q0007000800074Q0061000800024Q00623Q00013Q00013Q00063Q0003043Q004865616403053Q00737461747303043Q004669736803043Q005465787403083Q004D75746174696F6E03053Q004C6162656C000E4Q00693Q00013Q0020515Q00010020515Q00020020515Q00030020515Q00042Q00758Q00693Q00013Q0020515Q00010020515Q00020020515Q00050020515Q00060020515Q00042Q00753Q00024Q00623Q00017Q00053Q0003043Q007761726E03243Q005B4162792Q73616C5D2073657443616E436F2Q6C6964653A2063686172206973206E696C03063Q00697061697273030B3Q004765744368696C6472656E03053Q007063612Q6C02143Q0006353Q0006000100010004143Q00060001001254000200013Q00121A000300024Q00590002000200012Q00623Q00013Q001254000200033Q00208300033Q00042Q007E000300044Q004300023Q00040004143Q00110001001254000700053Q00066400083Q000100022Q003D3Q00064Q003D3Q00014Q00590007000200012Q001300055Q00062B0002000B000100020004143Q000B00012Q00623Q00013Q00013Q00033Q002Q033Q0049734103083Q004261736550617274030A3Q0043616E436F2Q6C696465000A4Q00697Q0020835Q000100121A000200024Q005C3Q000200020006803Q000900013Q0004143Q000900012Q00698Q0069000100013Q00102A3Q000300012Q00623Q00017Q00063Q0003093Q0043686172616374657203043Q007761726E03263Q005B4162792Q73616C5D207A65726F56656C6F636974793A20636861724F626A206973206E696C03063Q00697061697273030B3Q004765744368696C6472656E03053Q007063612Q6C01173Q0006160001000400013Q0004143Q000400012Q006900015Q0020510001000100010006350001000A000100010004143Q000A0001001254000200023Q00121A000300034Q00590002000200012Q00623Q00013Q001254000200043Q0020830003000100052Q007E000300044Q004300023Q00040004143Q00140001001254000700063Q00066400083Q000100012Q003D3Q00064Q00590007000200012Q001300055Q00062B0002000F000100020004143Q000F00012Q00623Q00013Q00013Q00053Q002Q033Q0049734103083Q00426173655061727403163Q00412Q73656D626C794C696E65617256656C6F6369747903073Q00566563746F723303043Q007A65726F000B4Q00697Q0020835Q000100121A000200024Q005C3Q000200020006803Q000A00013Q0004143Q000A00012Q00697Q001254000100043Q00205100010001000500102A3Q000300012Q00623Q00017Q00313Q0003063Q00506172656E7403043Q007761726E03343Q005B4162792Q73616C5D20736D2Q6F74684D6F7665546F3A20722Q6F74206973206E696C206F7220686173206E6F20706172656E7403093Q0043686172616374657203083Q00506F736974696F6E028Q0003053Q007072696E74032A3Q005B4162792Q73616C5D20736D2Q6F74684D6F7665546F2073746172746564202D3E207461726765743A2003083Q00746F737472696E67030A3Q00207C2073746570733A20026Q00F03F032B3Q005B4162792Q73616C5D20736D2Q6F74684D6F7665546F20696E74652Q727570746564206174207374657020033D3Q005B4162792Q73616C5D20736D2Q6F74684D6F7665546F3A2064657374506F73206F722063752Q72656E74506F73206973206E696C206174207374657020027Q004003063Q00747970656F6603073Q00566563746F723303093Q004D61676E6974756465026Q00244003063Q006E756D626572032B3Q005B4162792Q73616C5D20736D2Q6F74684D6F7665546F3A20737475636B20646574656374656420666F7220030E3Q00207C206D6F766564446973743A2003083Q00536166655A6F6E652Q0103173Q005B4162792Q73616C5D20426C61636B6C69737465643A2003063Q0020283135732903043Q007461736B03053Q0064656C6179026Q002E4003013Q005803013Q005903013Q005A03043Q006D61746803043Q007371727403333Q005B4162792Q73616C5D20736D2Q6F74684D6F7665546F3A2073746F7020636F6E646974696F6E206D657420617420646973742003053Q00666C2Q6F7203053Q0020666F72202Q033Q006E657703093Q00776F726B737061636503043Q0047616D6503053Q005475626573030E3Q0046696E6446697273744368696C6403043Q004E616D6503083Q00522Q6F7450617274025Q00804640026Q00144003053Q007063612Q6C030B3Q006D6F75736531636C69636B03043Q007761697403233Q005B4162792Q73616C5D20736D2Q6F74684D6F7665546F2066696E6973686564202D3E2006EF3Q0006803Q000500013Q0004143Q0005000100205100063Q00010006350006000B000100010004143Q000B0001001254000600023Q00121A000700034Q00590006000200012Q003000066Q007500066Q00623Q00014Q0069000600013Q00205100060006000400061600070010000100030004143Q001000012Q0069000700023Q00061600080013000100040004143Q001300012Q0069000800033Q00205100093Q000500121A000A00063Q001254000B00073Q00121A000C00083Q001254000D00094Q0007000E00054Q000B000D0002000200121A000E000A4Q0007000F00074Q0063000C000C000F2Q0059000B000200012Q0030000B00014Q0075000B6Q0069000B00044Q0007000C00064Q0030000D6Q002F000B000D000100121A000B000B4Q0007000C00073Q00121A000D000B3Q000465000B00DC00012Q0069000F00053Q000680000F002E00013Q0004143Q002E00012Q0069000F5Q000635000F0034000100010004143Q00340001001254000F00073Q00121A0010000C4Q00070011000E4Q00630010001000112Q0059000F000200010004143Q00DC00012Q0007000F00014Q0038000F0001000200205100103Q0005000680000F003B00013Q0004143Q003B000100063500100041000100010004143Q00410001001254001100023Q00121A0012000D4Q00070013000E4Q00630012001200132Q00590011000200010004143Q00DC00012Q0041000A000A0008000E7D000E00790001000A0004143Q0079000100121A001100063Q0012540012000F4Q0007001300104Q000B00120002000200261B00120052000100100004143Q005200010012540012000F4Q0007001300094Q000B00120002000200261B00120052000100100004143Q005200012Q00330012001000090020510011001200110004143Q0053000100121A001100123Q0012540012000F4Q0007001300114Q000B00120002000200261B00120077000100130004143Q0077000100261F001100770001000B0004143Q00770001001254001200023Q00121A001300143Q001254001400094Q0007001500054Q000B00140002000200121A001500154Q0007001600114Q00630013001300162Q0059001200020001000680000500DC00013Q0004143Q00DC000100264C000500DC000100160004143Q00DC00012Q0069001200063Q002060001200050017001254001200073Q00121A001300184Q0007001400053Q00121A001500194Q00630013001300152Q00590012000200010012540012001A3Q00205100120012001B00121A0013001C3Q00066400143Q000100022Q00763Q00064Q003D3Q00054Q002F0012001400010004143Q00DC00012Q0007000900103Q00121A000A00063Q0020510011000F001D00205100120010001D2Q00330011001100120020510012000F001E00205100130010001E2Q00330012001200130020510013000F001F00205100140010001F2Q0033001300130014001254001400203Q0020510014001400212Q00770015001100112Q00770016001200122Q00410015001500162Q00770016001300132Q00410015001500162Q000B0014000200020006800002009E00013Q0004143Q009E00012Q0007001500024Q0007001600144Q000B0015000200020006800015009E00013Q0004143Q009E0001001254001500073Q00121A001600223Q001254001700203Q0020510017001700232Q0007001800144Q000B00170002000200121A001800243Q001254001900094Q0007001A00054Q000B0019000200022Q00630016001600192Q00590015000200010004143Q00DC00012Q003300150007000E002Q2000150015000B0010220015000B0015001254001600103Q00205100160016002500205100170010001D0020510018000F001D00205100190010001D2Q00330018001800192Q00770018001800152Q004100170017001800205100180010001E0020510019000F001E002051001A0010001E2Q003300190019001A2Q00770019001900152Q004100180018001900205100190010001F002051001A000F001F002051001B0010001F2Q0033001A001A001B2Q0077001A001A00152Q004100190019001A2Q005C0016001900022Q0069001700074Q0007001800064Q005900170002000100102A3Q00050016001254001700263Q0020510017001700270020510017001700280020830017001700292Q0069001900013Q00205100190019002A2Q005C001700190002000680001700CA00013Q0004143Q00CA000100208300180017002900121A001A002B4Q005C0018001A0002000680001800CA00013Q0004143Q00CA000100205100180017002B00102A001800050016001254001800203Q0020510018001800212Q00770019001100112Q0077001A001300132Q004100190019001A2Q000B00180002000200261F001400D70001002C0004143Q00D70001000E03002D00D7000100180004143Q00D700010012540019002E3Q001254001A002F4Q00590019000200010012540019001A3Q0020510019001900302Q0007001A00084Q0059001900020001000405000B00280001001254000B00073Q00121A000C00313Q001254000D00094Q0007000E00054Q000B000D000200022Q0063000C000C000D2Q0059000B000200012Q0069000B00074Q0069000C00013Q002051000C000C00042Q0059000B000200012Q0069000B00044Q0069000C00013Q002051000C000C00042Q0030000D00014Q002F000B000D00012Q0030000B6Q0075000B6Q00623Q00013Q00013Q00034Q0003053Q007072696E7403193Q005B4162792Q73616C5D20556E626C61636B6C69737465643A2000094Q00698Q0069000100013Q0020603Q000100010012543Q00023Q00121A000100034Q0069000200014Q00630001000100022Q00593Q000200012Q00623Q00017Q001D3Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403043Q007761726E03303Q005B4162792Q73616C5D2074656C65706F7274546F3A2048756D616E6F6964522Q6F7450617274206E6F7420666F756E6403053Q007072696E74031A3Q005B4162792Q73616C5D2054656C65706F7274696E6720746F3A2003083Q00506F736974696F6E03013Q005803013Q005903013Q005A03043Q006D61746803043Q0073717274026Q0008402Q033Q006D6178026Q00244003053Q00666C2Q6F7202FCA9F1D24D62903F026Q00F03F03073Q00566563746F72332Q033Q006E657703093Q00776F726B737061636503043Q0047616D6503053Q00547562657303043Q004E616D6503083Q00522Q6F745061727403043Q007461736B03043Q0077616974031D3Q005B4162792Q73616C5D2054656C65706F727420636F6D706C6574653A2002804Q006900025Q00205100020002000100066E00030007000100020004143Q0007000100208300030002000200121A000500034Q005C0003000500020006350003000D000100010004143Q000D0001001254000400043Q00121A000500054Q00590004000200012Q00623Q00013Q001254000400063Q00121A000500074Q0007000600014Q00630005000500062Q00590004000200012Q0069000400014Q0007000500024Q003000066Q002F00040006000100205100040003000800205100053Q00090020510006000400092Q003300050005000600205100063Q000A00205100070004000A2Q003300060006000700205100073Q000B00205100080004000B2Q00330007000700080012540008000C3Q00205100080008000D2Q00770009000500052Q0077000A000600062Q004100090009000A2Q0077000A000700072Q004100090009000A2Q000B00080002000200121A0009000E3Q001254000A000C3Q002051000A000A000F00121A000B00103Q001254000C000C3Q002051000C000C00112Q007B000D000800092Q007E000C000D4Q0027000A3Q000200121A000B00123Q00121A000C00134Q0007000D000A3Q00121A000E00133Q000465000C006500012Q007B0010000F000A001254001100143Q00205100110011001500205100120004000900205100133Q00090020510014000400092Q00330013001300142Q00770013001300102Q004100120012001300205100130004000A00205100143Q000A00205100150004000A2Q00330014001400152Q00770014001400102Q004100130013001400205100140004000B00205100153Q000B00205100160004000B2Q00330015001500162Q00770015001500102Q00410014001400152Q005C0011001400022Q0069001200024Q0007001300024Q005900120002000100102A000300080011001254001200163Q0020510012001200170020510012001200180020830012001200022Q006900145Q0020510014001400192Q005C0012001400020006800012006000013Q0004143Q0060000100208300130012000200121A0015001A4Q005C0013001500020006800013006000013Q0004143Q0060000100205100130012001A00102A0013000800110012540013001B3Q00205100130013001C2Q00070014000B4Q0059001300020001000405000C0036000100102A000300083Q001254000C00163Q002051000C000C0017002051000C000C0018002083000C000C00022Q0069000E5Q002051000E000E00192Q005C000C000E0002000680000C007600013Q0004143Q00760001002083000D000C000200121A000F001A4Q005C000D000F0002000680000D007600013Q0004143Q00760001002051000D000C001A00102A000D00084Q0069000D00014Q0007000E00024Q0030000F00014Q002F000D000F0001001254000D00063Q00121A000E001D4Q0007000F00014Q0063000E000E000F2Q0059000D000200012Q00623Q00017Q000F3Q0003053Q007072696E7403283Q005B4162792Q73616C5D20506572666F726D616E6365207374617473206C2Q6F70207374617274656403043Q0067616D65030A3Q004765745365727669636503053Q00537461747303103Q00506572666F726D616E6365537461747303053Q007061697273030B3Q004765744368696C6472656E03043Q004E616D6503083Q00496E7465726E616C03073Q0052752Q6E696E6703043Q007461736B03043Q0077616974026Q00F03F03053Q007063612Q6C00243Q0012543Q00013Q00121A000100024Q00593Q000200010012543Q00033Q0020835Q000400121A000200054Q005C3Q000200020020515Q00062Q001C00015Q001254000200073Q00208300033Q00082Q007E000300044Q004300023Q00040004143Q001000010020510007000600092Q003A00010007000600062B0002000E000100020004143Q000E000100066400023Q000100012Q003D3Q00014Q006900035Q00205100030003000A00205100030003000B0006800003002300013Q0004143Q002300010012540003000C3Q00205100030003000D00121A0004000E4Q00590003000200010012540003000F3Q00066400040001000100022Q00763Q00014Q003D3Q00024Q00590003000200010004143Q001400012Q00623Q00013Q00023Q00073Q002Q033Q004E2F4103073Q00412Q6472652Q73030B3Q006D656D6F72795F7265616403063Q00737472696E67026Q006A40028Q00026Q006B40011A4Q006900016Q0017000100013Q00063500010006000100010004143Q0006000100121A000200014Q0061000200023Q002051000200010002001254000300033Q00121A000400043Q002Q200005000200052Q005C0003000500020006800003001100013Q0004143Q001100012Q0012000400033Q000E0300060011000100040004143Q001100012Q0061000300023Q001254000400033Q00121A000500043Q002Q200006000200072Q005C00040006000200061600050018000100040004143Q0018000100121A000500014Q0061000500024Q00623Q00017Q000F3Q0003063Q004D656D6F72792Q033Q0053657403083Q004D656D6F72793A202Q033Q0043505503053Q004350553A202Q033Q0047505503053Q004750553A2003043Q0050696E6703063Q0050696E673A2003093Q004E6574776F726B496E030C3Q004E6574776F726B20496E3A20030F3Q004E6574776F726B5265636569766564030A3Q004E6574776F726B4F7574030D3Q004E6574776F726B204F75743A20030B3Q004E6574776F726B53656E7400374Q00697Q0020515Q00010020835Q000200121A000200034Q0069000300013Q00121A000400014Q000B0003000200022Q00630002000200032Q002F3Q000200012Q00697Q0020515Q00040020835Q000200121A000200054Q0069000300013Q00121A000400044Q000B0003000200022Q00630002000200032Q002F3Q000200012Q00697Q0020515Q00060020835Q000200121A000200074Q0069000300013Q00121A000400064Q000B0003000200022Q00630002000200032Q002F3Q000200012Q00697Q0020515Q00080020835Q000200121A000200094Q0069000300013Q00121A000400084Q000B0003000200022Q00630002000200032Q002F3Q000200012Q00697Q0020515Q000A0020835Q000200121A0002000B4Q0069000300013Q00121A0004000C4Q000B0003000200022Q00630002000200032Q002F3Q000200012Q00697Q0020515Q000D0020835Q000200121A0002000E4Q0069000300013Q00121A0004000F4Q000B0003000200022Q00630002000200032Q002F3Q000200012Q00623Q00017Q00073Q0003053Q007072696E74031D3Q005B4162792Q73616C5D204175746F206661726D20746F2Q676C65643A2003083Q00746F737472696E67030A3Q006B657972656C65617365025Q0040524003093Q0043686172616374657203283Q005B4162792Q73616C5D204175746F206661726D2073746F2Q7065642C207374617465207265736574011D4Q00757Q001254000100013Q00121A000200023Q001254000300034Q000700046Q000B0003000200022Q00630002000200032Q00590001000200012Q006900015Q0006350001001C000100010004143Q001C0001001254000100043Q00121A000200054Q00590001000200012Q0069000100014Q00740001000100012Q0069000100024Q0069000200033Q0020510002000200062Q0030000300014Q002F0001000300012Q003000016Q0075000100044Q004F000100014Q0075000100053Q001254000100013Q00121A000200074Q00590001000200012Q00623Q00017Q00073Q0003053Q007072696E7403253Q005B4162792Q73616C5D204175746F206661726D206B657962696E6420746F2Q676C65643A2003083Q00746F737472696E67030A3Q006B657972656C65617365025Q0040524003093Q0043686172616374657203283Q005B4162792Q73616C5D204175746F206661726D2073746F2Q7065642C207374617465207265736574001F4Q00698Q000A8Q00757Q0012543Q00013Q00121A000100023Q001254000200034Q006900036Q000B0002000200022Q00630001000100022Q00593Q000200012Q00697Q0006353Q001E000100010004143Q001E00010012543Q00043Q00121A000100054Q00593Q000200012Q00693Q00014Q00743Q000100012Q00693Q00024Q0069000100033Q0020510001000100062Q0030000200014Q002F3Q000200012Q00308Q00753Q00044Q004F8Q00753Q00053Q0012543Q00013Q00121A000100074Q00593Q000200012Q00623Q00017Q00033Q0003053Q007072696E7403273Q005B4162792Q73616C5D204175746F6661726D206B657962696E64206368616E67656420746F3A2003083Q00746F737472696E6701083Q001254000100013Q00121A000200023Q001254000300034Q000700046Q000B0003000200022Q00630002000200032Q00590001000200012Q00623Q00017Q00043Q0003053Q007072696E7403203Q005B4162792Q73616C5D204661726D2061726561206368616E67656420746F3A2003083Q00207C20706F733A2003083Q00746F737472696E67010F4Q00758Q0069000100024Q006900026Q00170001000100022Q0075000100013Q001254000100013Q00121A000200024Q006900035Q00121A000400033Q001254000500044Q0069000600014Q000B0005000200022Q00630002000200052Q00590001000200012Q00623Q00017Q00033Q0003053Q007072696E7403233Q005B4162792Q73616C5D204F787967656E207468726573686F6C642073657420746F3A2003013Q002501084Q00757Q001254000100013Q00121A000200024Q000700035Q00121A000400034Q00630002000200042Q00590001000200012Q00623Q00017Q00073Q00028Q0003053Q007072696E74033B3Q005B4162792Q73616C5D204D75746174696F6E2066696C74657220636C6561726564202D20746172676574696E6720612Q6C206D75746174696F6E73031F3Q005B4162792Q73616C5D204D75746174696F6E2066696C746572207365743A2003053Q007461626C6503063Q00636F6E63617403023Q002C2001124Q00758Q001200015Q00261B00010008000100010004143Q00080001001254000100023Q00121A000200034Q00590001000200010004143Q00110001001254000100023Q00121A000200043Q001254000300053Q0020510003000300062Q000700045Q00121A000500074Q005C0003000500022Q00630002000200032Q00590001000200012Q00623Q00017Q00093Q0003063Q0069706169727303053Q007461626C6503063Q00696E73657274028Q0003053Q007072696E7403383Q005B4162792Q73616C5D204669736820747970652066696C74657220636C6561726564202D20746172676574696E6720612Q6C20747970657303203Q005B4162792Q73616C5D204669736820747970652066696C746572207365743A2003063Q00636F6E63617403023Q002C20012A4Q00758Q001C00015Q001254000200014Q006900036Q005A0002000200040004143Q000B0001001254000700023Q0020510007000700032Q0007000800014Q0007000900064Q002F00070009000100062B00020006000100020004143Q00060001001254000200014Q0069000300014Q005A0002000200040004143Q00160001001254000700023Q0020510007000700032Q0007000800014Q0007000900064Q002F00070009000100062B00020011000100020004143Q001100012Q0075000100024Q0012000200013Q00261B00020020000100040004143Q00200001001254000200053Q00121A000300064Q00590002000200010004143Q00290001001254000200053Q00121A000300073Q001254000400023Q0020510004000400082Q0007000500013Q00121A000600094Q005C0004000600022Q00630003000300042Q00590002000200012Q00623Q00017Q00093Q0003063Q0069706169727303053Q007461626C6503063Q00696E73657274028Q0003053Q007072696E7403383Q005B4162792Q73616C5D204669736820747970652066696C74657220636C6561726564202D20746172676574696E6720612Q6C20747970657303203Q005B4162792Q73616C5D204669736820747970652066696C746572207365743A2003063Q00636F6E63617403023Q002C20012A4Q00758Q001C00015Q001254000200014Q0069000300014Q005A0002000200040004143Q000B0001001254000700023Q0020510007000700032Q0007000800014Q0007000900064Q002F00070009000100062B00020006000100020004143Q00060001001254000200014Q006900036Q005A0002000200040004143Q00160001001254000700023Q0020510007000700032Q0007000800014Q0007000900064Q002F00070009000100062B00020011000100020004143Q001100012Q0075000100024Q0012000200013Q00261B00020020000100040004143Q00200001001254000200053Q00121A000300064Q00590002000200010004143Q00290001001254000200053Q00121A000300073Q001254000400023Q0020510004000400082Q0007000500013Q00121A000600094Q005C0004000600022Q00630003000300042Q00590002000200012Q00623Q00017Q00033Q002Q033Q0053657403053Q007072696E7403203Q005B4162792Q73616C5D20412Q6C20666973682066696C7465727320726573657400214Q001C8Q00758Q001C8Q00753Q00014Q001C8Q00753Q00024Q001C8Q00753Q00034Q00693Q00043Q0006803Q000F00013Q0004143Q000F00012Q00693Q00043Q0020835Q00012Q001C00026Q002F3Q000200012Q00693Q00053Q0006803Q001600013Q0004143Q001600012Q00693Q00053Q0020835Q00012Q001C00026Q002F3Q000200012Q00693Q00063Q0006803Q001D00013Q0004143Q001D00012Q00693Q00063Q0020835Q00012Q001C00026Q002F3Q000200010012543Q00023Q00121A000100034Q00593Q000200012Q00623Q00017Q00023Q0003053Q007072696E7403203Q005B4162792Q73616C5D2074772Q656E4475726174696F6E2073657420746F3A20010B4Q00758Q006900016Q0069000200024Q007B0001000100022Q0075000100013Q001254000100013Q00121A000200024Q000700036Q00630002000200032Q00590001000200012Q00623Q00017Q00043Q002Q033Q00536574026Q00084003053Q007072696E74032B3Q005B4162792Q73616C5D2074772Q656E4475726174696F6E20726573657420746F2064656661756C743A203300084Q00697Q0020835Q000100121A000200024Q002F3Q000200010012543Q00033Q00121A000100044Q00593Q000200012Q00623Q00017Q00023Q0003053Q007072696E7403293Q005B4162792Q73616C5D207265747265617453702Q65644D756C7469706C6965722073657420746F3A2001074Q00757Q001254000100013Q00121A000200024Q000700036Q00630002000200032Q00590001000200012Q00623Q00017Q00043Q002Q033Q00536574027Q004003053Q007072696E7403343Q005B4162792Q73616C5D207265747265617453702Q65644D756C7469706C69657220726573657420746F2064656661756C743A203200084Q00697Q0020835Q000100121A000200024Q002F3Q000200010012543Q00033Q00121A000100044Q00593Q000200012Q00623Q00017Q00023Q0003053Q007072696E74031A3Q005B4162792Q73616C5D206D696E446973742073657420746F3A2001074Q00757Q001254000100013Q00121A000200024Q000700036Q00630002000200032Q00590001000200012Q00623Q00017Q00043Q002Q033Q00536574026Q00394003053Q007072696E7403263Q005B4162792Q73616C5D206D696E4469737420726573657420746F2064656661756C743A20323500084Q00697Q0020835Q000100121A000200024Q002F3Q000200010012543Q00033Q00121A000100044Q00593Q000200012Q00623Q00017Q00023Q0003053Q007072696E74031D3Q005B4162792Q73616C5D2074772Q656E53746570732073657420746F3A20010B4Q00758Q0069000100024Q006900026Q007B0001000100022Q0075000100013Q001254000100013Q00121A000200024Q000700036Q00630002000200032Q00590001000200012Q00623Q00017Q00043Q002Q033Q00536574026Q003E4003053Q007072696E7403293Q005B4162792Q73616C5D2074772Q656E537465707320726573657420746F2064656661756C743A20333000084Q00697Q0020835Q000100121A000200024Q002F3Q000200010012543Q00033Q00121A000100044Q00593Q000200012Q00623Q00017Q00043Q0003053Q007072696E7403233Q005B4162792Q73616C5D2054656C65706F72742062752Q746F6E207072652Q7365643A2003043Q007461736B03053Q00737061776E000D3Q0012543Q00013Q00121A000100024Q006900026Q00630001000100022Q00593Q000200010012543Q00033Q0020515Q000400066400013Q000100032Q00763Q00014Q00763Q00024Q00768Q00593Q000200012Q00623Q00013Q00018Q00054Q00698Q0069000100014Q0069000200024Q002F3Q000200012Q00623Q00017Q00043Q0003053Q007072696E74031B3Q005B4162792Q73616C5D204E6F2D636C69702061637469766174656403043Q007461736B03053Q00737061776E00093Q0012543Q00013Q00121A000100024Q00593Q000200010012543Q00033Q0020515Q000400066400013Q000100012Q00768Q00593Q000200012Q00623Q00013Q00013Q001B3Q0003093Q00776F726B7370616365030E3Q0046696E6446697273744368696C642Q033Q004D617003063Q00646562726973030E3Q0047657444657363656E64616E7473026Q00F03F2Q033Q0049734103083Q004261736550617274030A3Q0043616E436F2Q6C696465010003053Q007063612Q6C03063Q00506172656E74025Q00408F40028Q0003043Q007461736B03043Q007761697403043Q007761726E03203Q005B4162792Q73616C5D204E6F2D636C69703A204D6170206E6F7420666F756E6403093Q0043686172616374657203063Q0069706169727303053Q007072696E7403233Q005B4162792Q73616C5D204E6F2D636C69703A2048756D616E6F6964522Q6F745061727403043Q0047616D6503053Q00547562657303043Q004E616D6503173Q005B4162792Q73616C5D204E6F2D636C69703A205475626503193Q005B4162792Q73616C5D204E6F2D636C69703A204C6F61646564005D3Q0012543Q00013Q0020835Q000200121A000200034Q005C3Q00020002001254000100013Q00208300010001000200121A000300044Q005C0001000300020006803Q002700013Q0004143Q002700010006800001002700013Q0004143Q0027000100208300023Q00052Q000B00020002000200121A000300064Q0012000400023Q00121A000500063Q0004650003002600012Q001700070002000600208300080007000700121A000A00084Q005C0008000A00020006800008001E00013Q0004143Q001E000100302100070009000A0012540008000B3Q00066400093Q000100012Q003D3Q00074Q005900080002000100102A0007000C000100205800080006000D00261B000800240001000E0004143Q002400010012540008000F3Q0020510008000800102Q00740008000100012Q001300075Q0004050003001200010004143Q002A0001001254000200113Q00121A000300124Q00590002000200012Q006900025Q0020510002000200130006800002004000013Q0004143Q00400001001254000200144Q006900035Q0020510003000300130020830003000300052Q007E000300044Q004300023Q00040004143Q003B000100208300070006000700121A000900084Q005C0007000900020006800007003B00013Q0004143Q003B000100302100060009000A00062B00020035000100020004143Q00350001001254000200153Q00121A000300164Q0059000200020001001254000200013Q0020510002000200170020510002000200180020830002000200022Q006900045Q0020510004000400192Q005C0002000400020006800002005900013Q0004143Q00590001001254000300143Q0020830004000200052Q007E000400054Q004300033Q00050004143Q0054000100208300080007000700121A000A00084Q005C0008000A00020006800008005400013Q0004143Q0054000100302100070009000A00062B0003004E000100020004143Q004E0001001254000300153Q00121A0004001A4Q0059000300020001001254000300153Q00121A0004001B4Q00590003000200012Q00623Q00013Q00013Q00033Q0003083Q0043616E5175657279010003083Q0043616E546F75636800054Q00697Q0030213Q000100022Q00697Q0030213Q000300022Q00623Q00017Q00063Q0003053Q007072696E74031D3Q005B4162792Q73616C5D2043616D657261206C2Q6F70207374617274656403043Q007461736B03043Q007761697402B81E85EB51B89E3F03053Q007063612Q6C00133Q0012543Q00013Q00121A000100024Q00593Q000200010012543Q00033Q0020515Q000400121A000100054Q00593Q000200012Q00697Q0006803Q000300013Q0004143Q000300012Q00693Q00013Q0006803Q000300013Q0004143Q000300010012543Q00063Q00066400013Q000100012Q00763Q00014Q00593Q000200010004143Q000300012Q00623Q00013Q00013Q00083Q00030E3Q0046696E6446697273744368696C6403043Q004865616403083Q00522Q6F7450617274030B3Q005072696D6172795061727403093Q00776F726B7370616365030D3Q0043752Q72656E7443616D65726103063Q006C2Q6F6B417403083Q00506F736974696F6E00194Q00697Q0020835Q000100121A000200024Q005C3Q000200020006353Q000E000100010004143Q000E00012Q00697Q0020835Q000100121A000200034Q005C3Q000200020006353Q000E000100010004143Q000E00012Q00697Q0020515Q00040006803Q001800013Q0004143Q00180001001254000100053Q002051000100010006002051000100010007001254000200053Q00205100020002000600205100020002000800205100033Q00082Q002F0001000300012Q00623Q00017Q00093Q0003053Q007072696E7403213Q005B4162792Q73616C5D204175746F2D6361746368206C2Q6F70207374617274656403043Q007461736B03043Q0077616974026Q00F03F03053Q007063612Q6C03043Q007761726E031C3Q005B4162792Q73616C5D204175746F2D636174636820652Q726F723A2003083Q00746F737472696E6700193Q0012543Q00013Q00121A000100024Q00593Q000200010012543Q00033Q0020515Q000400121A000100054Q00593Q000200012Q00697Q0006803Q000300013Q0004143Q000300010012543Q00063Q00066400013Q000100012Q00763Q00014Q005A3Q000200010006353Q0003000100010004143Q00030001001254000200073Q00121A000300083Q001254000400094Q0007000500014Q000B0004000200022Q00630003000300042Q00590002000200010004143Q000300012Q00623Q00013Q00013Q00133Q0003093Q00506C6179657247756903043Q004D61696E030B3Q004361746368696E6742617203053Q004672616D652Q033Q0042617203053Q00436174636803053Q0047722Q656E03073Q00412Q6472652Q73030C3Q006D656D6F72795F777269746503053Q00666C6F6174025Q00E09440026Q00F03F025Q00F09440026Q009540025Q0010954003053Q007072696E74032D3Q005B4162792Q73616C5D204175746F2D63617463683A206D656D6F7279207772692Q74656E20617420626173652003043Q007761726E03283Q005B4162792Q73616C5D204175746F2D63617463683A20636F6E74726F6C42617365206973206E696C00294Q00697Q0020515Q00010020515Q00020020515Q00030020515Q00040020515Q000500205100013Q00060020510001000100070020510001000100080006800001002500013Q0004143Q00250001001254000200093Q00121A0003000A3Q002Q2000040001000B00121A0005000C4Q002F000200050001001254000200093Q00121A0003000A3Q002Q2000040001000D00121A0005000C4Q002F000200050001001254000200093Q00121A0003000A3Q002Q2000040001000E00121A0005000C4Q002F000200050001001254000200093Q00121A0003000A3Q002Q2000040001000F00121A0005000C4Q002F000200050001001254000200103Q00121A000300114Q0007000400014Q00630003000300042Q00590002000200010004143Q00280001001254000200123Q00121A000300134Q00590002000200012Q00623Q00017Q00503Q0003053Q007072696E74031C3Q005B4162792Q73616C5D204D61696E206379636C652073746172746564028Q0003043Q007461736B03043Q007761697402B81E85EB51B89E3F03083Q006B65797072652Q73025Q0040524003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403043Q007761726E03303Q005B4162792Q73616C5D204D61696E206379636C653A2048756D616E6F6964522Q6F7450617274206E6F7420666F756E6403093Q00506C6179657247756903043Q004D61696E03063Q004F787967656E03293Q005B4162792Q73616C5D204D61696E206379636C653A204F787967656E205549206E6F7420666F756E6403083Q00746F6E756D626572030C3Q00476574412Q7472696275746503093Q006F6C646F787967656E026Q00594003163Q005B4162792Q73616C5D204E6577206D61784F78793A20027Q0040030F3Q005B4162792Q73616C5D204F78793A2003043Q006D61746803053Q00666C2Q6F7203013Q002F03023Q00202803103Q002529207C207468726573686F6C643A2003103Q0025207C2072657472656174696E673A2003083Q00746F737472696E6703353Q005B4162792Q73616C5D204C4F57204F585947454E2C2052657472656174696E6720746F2073616665207A6F6E65207C206F78793A2003013Q0025026Q005640029A5Q99A93F030A3Q006B657972656C65617365025Q00805840031B3Q005B4162792Q73616C5D204F787967656E20726573746F726564202803113Q0025292C20726573756D696E67206661726D026Q004E4003083Q00536166655A6F6E6503093Q00776F726B737061636503043Q0047616D6503043Q004669736803063Q00636C69656E74033D3Q005B4162792Q73616C5D204669736820666F6C646572206E6F7420666F756E6420617420776F726B73706163652E47616D652E466973682E636C69656E74024Q007E842E4103083Q00506F736974696F6E03063Q00697061697273030B3Q004765744368696C6472656E026Q00F03F03043Q004E616D6503043Q004865616403083Q00522Q6F7450617274030B3Q005072696D6172795061727403013Q005803013Q005903013Q005A03043Q007371727403103Q005B4162792Q73616C5D205363616E3A2003093Q0020746F74616C207C20030F3Q0020626C61636B6C6973746564207C2003153Q002066696C7465726564207C20636C6F736573743A2003043Q006E6F6E6503093Q002061742064697374202Q033Q006E2F6103013Q003F03053Q007063612Q6C03163Q005B4162792Q73616C5D204E6577207461726765743A20030A3Q0029207C20646973743A2003063Q00506172656E74031A3Q005B4162792Q73616C5D204D6F76696E6720746F20666973683A2003093Q00207C20646973743A2003053Q00737061776E026Q00144003233Q005B4162792Q73616C5D20496E2072616E67652C20636C69636B696E6720666973683A20030B3Q006D6F75736531636C69636B03243Q005B4162792Q73616C5D205461726765742066697368207061727420696E76616C69643A2000033F3Q005B4162792Q73616C5D204E6F2076616C696420746172676574206669736820666F756E64202866696C746572206D617920626520742Q6F20737472696374290081012Q0012543Q00013Q00121A000100024Q00593Q000200012Q004F7Q00121A000100033Q001254000200043Q00205100020002000500121A000300064Q00590002000200012Q006900025Q0006800002000500013Q0004143Q000500012Q0069000200013Q0006800002001000013Q0004143Q001000010004143Q00050001001254000200073Q00121A000300084Q00590002000200012Q0069000200023Q00205100020002000900066E0003001A000100020004143Q001A000100208300030002000A00121A0005000B4Q005C00030005000200063500030020000100010004143Q002000010012540004000C3Q00121A0005000D4Q00590004000200010004143Q000500012Q0069000400023Q00205100040004000E00205100040004000F00208300040004000A00121A000600104Q005C0004000600020006350004002B000100010004143Q002B00010012540005000C3Q00121A000600114Q00590005000200010006800004003400013Q0004143Q00340001001254000500123Q00208300060004001300121A000800144Q006D000600084Q002700053Q000200063500050035000100010004143Q0035000100121A000500154Q0069000600033Q00062Q0006003E000100050004143Q003E00012Q0075000500033Q001254000600013Q00121A000700164Q0069000800034Q00630007000700082Q00590006000200012Q0069000600033Q000E0300030044000100060004143Q004400012Q0069000600033Q00063500060045000100010004143Q0045000100121A000600154Q007B000700050006002034000700070015002Q20000100010006000E7D00170060000100010004143Q00600001001254000800013Q00121A000900183Q001254000A00193Q002051000A000A001A2Q0007000B00054Q000B000A0002000200121A000B001B4Q0007000C00063Q00121A000D001C3Q001254000E00193Q002051000E000E001A2Q0007000F00074Q000B000E0002000200121A000F001D4Q0069001000043Q00121A0011001E3Q0012540012001F4Q0069001300054Q000B0012000200022Q00630009000900122Q005900080002000100121A000100033Q0006800004007E00013Q0004143Q007E00012Q0069000800043Q0006180007007E000100080004143Q007E00012Q0069000800053Q0006350008007E000100010004143Q007E00012Q0030000800014Q0075000800053Q001254000800013Q00121A000900203Q001254000A00193Q002051000A000A001A2Q0007000B00074Q000B000A0002000200121A000B00214Q006300090009000B2Q0059000800020001001254000800073Q00121A000900224Q0059000800020001001254000800043Q00205100080008000500121A000900234Q0059000800020001001254000800243Q00121A000900224Q00590008000200010004143Q008E0001000E7D0025008E000100070004143Q008E00012Q0069000800053Q0006800008008E00013Q0004143Q008E00012Q003000086Q0075000800053Q001254000800013Q00121A000900263Q001254000A00193Q002051000A000A001A2Q0007000B00074Q000B000A0002000200121A000B00274Q006300090009000B2Q00590008000200012Q0069000800053Q0006800008009F00013Q0004143Q009F00012Q004F000800084Q0075000800064Q0069000800074Q0007000900033Q000664000A3Q000100012Q00763Q00084Q004F000B000B3Q00121A000C00284Q0069000D00094Q0069000E000A4Q007B000D000D000E00121A000E00294Q002F0008000E00010004143Q000500010012540008002A3Q00205100080008002B00205100080008002C00205100080008002D000635000800A9000100010004143Q00A900010012540009000C3Q00121A000A002E4Q00590009000200010004143Q000500012Q004F000900093Q00121A000A002F3Q002051000B0003003000121A000C00033Q00121A000D00033Q00121A000E00033Q001254000F00313Q0020830010000800322Q007E001000114Q0043000F3Q00110004143Q00E90001002Q20000C000C00332Q00690014000B3Q0020510015001300342Q0017001400140015000635001400E8000100010004143Q00E800012Q00690014000C4Q0007001500134Q000B001400020002000680001400E600013Q0004143Q00E6000100208300140013000A00121A001600354Q005C001400160002000635001400CA000100010004143Q00CA000100208300140013000A00121A001600364Q005C001400160002000635001400CA000100010004143Q00CA0001002051001400130037000680001400E900013Q0004143Q00E90001002051001500140030000680001500E900013Q0004143Q00E900010020510015001400300020510016001500380020510017000B00382Q00330016001600170020510017001500390020510018000B00392Q003300170017001800205100180015003A0020510019000B003A2Q0033001800180019001254001900193Q00205100190019003B2Q0077001A001600162Q0077001B001700172Q0041001A001A001B2Q0077001B001800182Q0041001A001A001B2Q000B00190002000200062Q001900E90001000A0004143Q00E900012Q0007000A00194Q0007000900133Q0004143Q00E90001002Q20000E000E00330004143Q00E90001002Q20000D000D003300062B000F00B4000100020004143Q00B4000100261B000100072Q0100030004143Q00072Q01001254000F00013Q00121A0010003C4Q00070011000C3Q00121A0012003D4Q00070013000D3Q00121A0014003E4Q00070015000E3Q00121A0016003F3Q000680000900FA00013Q0004143Q00FA0001002051001700090034000635001700FB000100010004143Q00FB000100121A001700403Q00121A001800413Q000680000900042Q013Q0004143Q00042Q01001254001900193Q00205100190019001A2Q0007001A000A4Q000B001900020002000635001900052Q0100010004143Q00052Q0100121A001900424Q00630010001000192Q0059000F00020001000680000900752Q013Q0004143Q00752Q012Q0075000900063Q002051000F000900340006463Q00232Q01000F0004143Q00232Q0100121A000F00433Q00121A001000433Q001254001100443Q00066400120001000100032Q003D3Q000F4Q003D3Q00094Q003D3Q00104Q0059001100020001001254001100013Q00121A001200454Q00070013000F3Q00121A0014001C4Q0007001500103Q00121A001600463Q001254001700193Q00205100170017001A2Q00070018000A4Q000B0017000200022Q00630012001200172Q00590011000200010020513Q000900342Q0013000F5Q002083000F0009000A00121A001100354Q005C000F00110002000635000F002E2Q0100010004143Q002E2Q01002083000F0009000A00121A001100364Q005C000F00110002000635000F002E2Q0100010004143Q002E2Q01002051000F00090037000680000F006F2Q013Q0004143Q006F2Q010020510010000F00470006800010006F2Q013Q0004143Q006F2Q010020510010000F00300006800010006F2Q013Q0004143Q006F2Q010020510010000F00300020510011001000380020510012000B00382Q00330011001100120020510012001000390020510013000B00392Q003300120012001300205100130010003A0020510014000B003A2Q0033001300130014001254001400193Q00205100140014003B2Q00770015001100112Q00770016001200122Q00410015001500162Q00770016001300132Q00410015001500162Q000B0014000200022Q00690015000D3Q00062Q0015005E2Q0100140004143Q005E2Q01001254001500013Q00121A001600483Q00205100170009003400121A001800493Q001254001900193Q00205100190019001A2Q0007001A00144Q000B0019000200022Q00630016001600192Q0059001500020001001254001500043Q00205100150015004A00066400160002000100042Q00763Q00074Q003D3Q00034Q003D3Q00094Q00763Q000D4Q00590015000200010004143Q007B2Q01001254001500193Q00205100150015003B2Q00770016001100112Q00770017001300132Q00410016001600172Q000B001500020002000E03004B007B2Q0100150004143Q007B2Q01001254001500013Q00121A0016004C3Q0020510017000900342Q00630016001600172Q0059001500020001001254001500443Q0012540016004D4Q00590015000200010004143Q007B2Q010012540010000C3Q00121A0011004E3Q0020510012000900342Q00630011001100122Q00590010000200010004143Q007B2Q0100264C3Q007B2Q01004F0004143Q007B2Q01001254000F00013Q00121A001000504Q0059000F000200012Q004F8Q001300025Q0004143Q000500012Q001300025Q0004143Q000500010004143Q000500012Q00623Q00013Q00038Q00034Q00698Q00613Q00024Q00623Q00017Q00063Q0003043Q004865616403053Q00737461747303043Q004669736803043Q005465787403083Q004D75746174696F6E03053Q004C6162656C000E4Q00693Q00013Q0020515Q00010020515Q00020020515Q00030020515Q00042Q00758Q00693Q00013Q0020515Q00010020515Q00020020515Q00050020515Q00060020515Q00042Q00753Q00024Q00623Q00017Q00013Q0003043Q004E616D65000D4Q00698Q0069000100013Q00066400023Q000100012Q00763Q00023Q00066400030001000100032Q00763Q00024Q00763Q00014Q00763Q00034Q004F000400054Q0069000600023Q0020510006000600012Q002F3Q000600012Q00623Q00013Q00023Q000C3Q0003063Q00506172656E74030E3Q0046696E6446697273744368696C6403043Q004865616403083Q00522Q6F7450617274030B3Q005072696D6172795061727403083Q00506F736974696F6E03073Q00566563746F72332Q033Q006E657703013Q0058026Q00244003013Q005903013Q005A00284Q00697Q0006803Q002500013Q0004143Q002500012Q00697Q0020515Q00010006803Q002500013Q0004143Q002500012Q00697Q0020835Q000200121A000200034Q005C3Q000200020006353Q0015000100010004143Q001500012Q00697Q0020835Q000200121A000200044Q005C3Q000200020006353Q0015000100010004143Q001500012Q00697Q0020515Q00050006803Q002500013Q0004143Q0025000100205100013Q00060006800001002500013Q0004143Q00250001001254000100073Q00205100010001000800205100023Q0006002051000200020009002Q2000020002000A00205100033Q000600205100030003000B00205100043Q000600205100040004000C2Q0026000100044Q004000016Q004F8Q00613Q00024Q00623Q00017Q00093Q00030E3Q0046696E6446697273744368696C6403043Q004865616403083Q00522Q6F7450617274030B3Q005072696D6172795061727403083Q00506F736974696F6E03043Q006D6174682Q033Q0061627303013Q0059026Q002040012E4Q006900015Q0006800001001100013Q0004143Q001100012Q006900015Q00208300010001000100121A000300024Q005C00010003000200063500010011000100010004143Q001100012Q006900015Q00208300010001000100121A000300034Q005C00010003000200063500010011000100010004143Q001100012Q006900015Q0020510001000100040006800001002700013Q0004143Q002700010020510002000100050006800002002700013Q0004143Q00270001001254000200063Q0020510002000200072Q0069000300013Q0020510003000300050020510003000300080020510004000100050020510004000400082Q00330003000300042Q000B0002000200022Q0069000300023Q0006183Q0024000100030004143Q0024000100262D00020025000100090004143Q002500012Q003C00036Q0030000300014Q0061000300024Q0069000200023Q0006713Q0002000100020004143Q002B00012Q003C00026Q0030000200014Q0061000200024Q00623Q00017Q00", GetFEnv(), ...);