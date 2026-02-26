-- @ptacunit, build: alpha
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
										if (Enum == 0) then
											local A = Inst[2];
											local B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
										else
											Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
										end
									elseif (Enum == 2) then
										if (Stk[Inst[2]] ~= Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local B = Inst[3];
										local K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
									end
								elseif (Enum <= 5) then
									if (Enum == 4) then
										Stk[Inst[2]] = Upvalues[Inst[3]];
									else
										local B = Stk[Inst[4]];
										if B then
											VIP = VIP + 1;
										else
											Stk[Inst[2]] = B;
											VIP = Inst[3];
										end
									end
								elseif (Enum > 6) then
									Stk[Inst[2]] = Env[Inst[3]];
								else
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								end
							elseif (Enum <= 11) then
								if (Enum <= 9) then
									if (Enum > 8) then
										local A = Inst[2];
										local Results, Limit = _R(Stk[A](Stk[A + 1]));
										Top = (Limit + A) - 1;
										local Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
									else
										Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									end
								elseif (Enum > 10) then
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
								end
							elseif (Enum <= 13) then
								if (Enum == 12) then
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								elseif (Stk[Inst[2]] < Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 14) then
								VIP = Inst[3];
							else
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							end
						elseif (Enum <= 23) then
							if (Enum <= 19) then
								if (Enum <= 17) then
									if (Enum > 16) then
										do
											return Stk[Inst[2]];
										end
									else
										do
											return Stk[Inst[2]];
										end
									end
								elseif (Enum > 18) then
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
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								end
							elseif (Enum <= 21) then
								if (Enum == 20) then
									do
										return;
									end
								else
									local A = Inst[2];
									local T = Stk[A];
									local B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								end
							elseif (Enum > 22) then
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
							end
						elseif (Enum <= 27) then
							if (Enum <= 25) then
								if (Enum == 24) then
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
										if (Mvm[1] == 107) then
											Indexes[Idx - 1] = {Stk,Mvm[3]};
										else
											Indexes[Idx - 1] = {Upvalues,Mvm[3]};
										end
										Lupvals[#Lupvals + 1] = Indexes;
									end
									Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
								elseif (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 26) then
								Stk[Inst[2]] = Inst[3] ~= 0;
							elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 29) then
							if (Enum > 28) then
								if (Stk[Inst[2]] > Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 30) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
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
					elseif (Enum <= 47) then
						if (Enum <= 39) then
							if (Enum <= 35) then
								if (Enum <= 33) then
									if (Enum == 32) then
										if (Stk[Inst[2]] > Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = VIP + Inst[3];
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
								elseif (Enum > 34) then
									Stk[Inst[2]] = Inst[3];
								else
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								end
							elseif (Enum <= 37) then
								if (Enum == 36) then
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								else
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								end
							elseif (Enum > 38) then
								local A = Inst[2];
								Stk[A] = Stk[A]();
							else
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 43) then
							if (Enum <= 41) then
								if (Enum == 40) then
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
									local A = Inst[2];
									local T = Stk[A];
									for Idx = A + 1, Inst[3] do
										Insert(T, Stk[Idx]);
									end
								end
							elseif (Enum == 42) then
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
							else
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
							end
						elseif (Enum <= 45) then
							if (Enum > 44) then
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
									if (Mvm[1] == 107) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							else
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum == 46) then
							if (Inst[2] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						end
					elseif (Enum <= 55) then
						if (Enum <= 51) then
							if (Enum <= 49) then
								if (Enum > 48) then
									if (Inst[2] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								end
							elseif (Enum > 50) then
								if (Stk[Inst[2]] > Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 53) then
							if (Enum > 52) then
								Stk[Inst[2]] = Inst[3];
							else
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							end
						elseif (Enum > 54) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							Stk[Inst[2]][Inst[3]] = Inst[4];
						end
					elseif (Enum <= 59) then
						if (Enum <= 57) then
							if (Enum == 56) then
								VIP = Inst[3];
							elseif Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 58) then
							Upvalues[Inst[3]] = Stk[Inst[2]];
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
					elseif (Enum <= 61) then
						if (Enum == 60) then
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						else
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 62) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					elseif (Enum > 63) then
						Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
					elseif (Stk[Inst[2]] == Inst[4]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 96) then
					if (Enum <= 80) then
						if (Enum <= 72) then
							if (Enum <= 68) then
								if (Enum <= 66) then
									if (Enum > 65) then
										local A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									else
										Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
									end
								elseif (Enum > 67) then
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								elseif (Stk[Inst[2]] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 70) then
								if (Enum == 69) then
									if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
								end
							elseif (Enum > 71) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							else
								Stk[Inst[2]] = Inst[3] ~= 0;
							end
						elseif (Enum <= 76) then
							if (Enum <= 74) then
								if (Enum == 73) then
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
									Stk[Inst[2]] = Inst[3] / Stk[Inst[4]];
								end
							elseif (Enum == 75) then
								if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 78) then
							if (Enum == 77) then
								local B = Stk[Inst[4]];
								if B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum > 79) then
							local B = Stk[Inst[4]];
							if not B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
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
					elseif (Enum <= 88) then
						if (Enum <= 84) then
							if (Enum <= 82) then
								if (Enum > 81) then
									local A = Inst[2];
									Stk[A](Stk[A + 1]);
								else
									Stk[Inst[2]] = #Stk[Inst[3]];
								end
							elseif (Enum > 83) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, A + Inst[3]);
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							end
						elseif (Enum <= 86) then
							if (Enum > 85) then
								if (Stk[Inst[2]] < Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 87) then
							local A = Inst[2];
							local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							Stk[Inst[2]] = not Stk[Inst[3]];
						end
					elseif (Enum <= 92) then
						if (Enum <= 90) then
							if (Enum > 89) then
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							else
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum == 91) then
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						else
							Stk[Inst[2]][Inst[3]] = Inst[4];
						end
					elseif (Enum <= 94) then
						if (Enum > 93) then
							Stk[Inst[2]] = Inst[3] / Stk[Inst[4]];
						else
							Stk[Inst[2]] = {};
						end
					elseif (Enum > 95) then
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
						Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
					end
				elseif (Enum <= 112) then
					if (Enum <= 104) then
						if (Enum <= 100) then
							if (Enum <= 98) then
								if (Enum > 97) then
									local A = Inst[2];
									Stk[A] = Stk[A]();
								elseif (Inst[2] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 99) then
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							elseif (Inst[2] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 102) then
							if (Enum > 101) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								local B = Inst[3];
								local K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
							end
						elseif (Enum == 103) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							Upvalues[Inst[3]] = Stk[Inst[2]];
						end
					elseif (Enum <= 108) then
						if (Enum <= 106) then
							if (Enum == 105) then
								Stk[Inst[2]]();
							else
								Stk[Inst[2]] = #Stk[Inst[3]];
							end
						elseif (Enum > 107) then
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]];
						end
					elseif (Enum <= 110) then
						if (Enum == 109) then
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
						elseif (Stk[Inst[2]] ~= Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum == 111) then
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
					elseif not Stk[Inst[2]] then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 120) then
					if (Enum <= 116) then
						if (Enum <= 114) then
							if (Enum == 113) then
								Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
							else
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							end
						elseif (Enum > 115) then
							Stk[Inst[2]] = Env[Inst[3]];
						elseif (Stk[Inst[2]] <= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 118) then
						if (Enum == 117) then
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
						else
							Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
						end
					elseif (Enum > 119) then
						if (Inst[2] < Stk[Inst[4]]) then
							VIP = Inst[3];
						else
							VIP = VIP + 1;
						end
					else
						local A = Inst[2];
						local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
						local Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					end
				elseif (Enum <= 124) then
					if (Enum <= 122) then
						if (Enum > 121) then
							Stk[Inst[2]] = not Stk[Inst[3]];
						else
							Stk[Inst[2]] = {};
						end
					elseif (Enum == 123) then
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
				elseif (Enum <= 126) then
					if (Enum == 125) then
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
						local A = Inst[2];
						local T = Stk[A];
						local B = Inst[3];
						for Idx = 1, B do
							T[Idx] = Stk[A + Idx];
						end
					end
				elseif (Enum <= 127) then
					if (Inst[2] < Stk[Inst[4]]) then
						VIP = Inst[3];
					else
						VIP = VIP + 1;
					end
				elseif (Enum > 128) then
					Stk[Inst[2]]();
				elseif (Stk[Inst[2]] > Stk[Inst[4]]) then
					VIP = VIP + 1;
				else
					VIP = VIP + Inst[3];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!05012Q0003043Q0067616D65030A3Q004765745365727669636503073Q00506C6179657273030B3Q004C6F63616C506C6179657203103Q0055736572496E7075745365727669636503053Q007072696E74031C3Q005B4162792Q73616C5D20536372697074207374617274696E673Q2E030E3Q00466F72676F2Q74656E20442Q657003073Q00566563746F72332Q033Q006E6577021F85EB51B8FE57C002F853E3A51B10B3402Q022B8716D90E27C0030D3Q00416E6369656E742053616E6473024Q33B3E09BC002B81E85EB912DB14002FCA9F1D24DA22F40030C3Q0053756E6B656E2057696C647302736891ED7C40ADC0024Q33731DA340026891ED7CFFB2B3C0030C3Q0053706972697420522Q6F74730248E17A14AEFE994002378941602583AF4002F6285C8FC2E59DC0031D3Q005B4162792Q73616C5D2044656661756C74206661726D20617265613A20028Q00026Q005440026Q002440026Q000840027Q0040026Q003940026Q003E40031E3Q005B4162792Q73616C5D2053652Q74696E677320696E697469616C697A656403223Q005B4162792Q73616C5D3Q206F78795468726573686F6C6450657263656E74203D20031C3Q005B4162792Q73616C5D3Q2074772Q656E4475726174696F6E203D2003163Q005B4162792Q73616C5D3Q206D696E44697374203D2003193Q005B4162792Q73616C5D2048656C7065727320646566696E656403213Q005B4162792Q73616C5D204D6F76656D656E7420656E67696E6520646566696E6564031F3Q005B4162792Q73616C5D204C6F6164696E67205549206C6962726172793Q2E030A3Q006C6F6164737472696E6703073Q00482Q747047657403443Q00682Q7470733A2Q2F7261772E67697468756275736572636F6E74656E742E636F6D2F7A2Q652D373635342F55492F726566732F68656164732F6D61696E2F55492E6C756103223Q005B4162792Q73616C5D205549206C696272617279206C6F616465642C205549203D2003083Q00746F737472696E6703023Q00554903063Q006E6F74696679030C3Q004162792Q73616C204D656E7503093Q005549204C6F6164656403063Q0057696E646F7703053Q005469746C6503243Q004162792Q73616C204D656E75207C204275696C643A20416C706861207C204D617463686103043Q0053697A6503073Q00566563746F7232025Q00407F40025Q00E0754003043Q004F70656E2Q0103053Q005468656D6503063Q00476C6F62616C030B3Q004C69676874412Q63656E7403063Q00436F6C6F723303073Q0066726F6D524742026Q005940026Q006940025Q00E06F4003063Q00412Q63656E74026Q004940026Q005E40025Q00806B40030A3Q004461726B412Q63656E74025Q00805140025Q00C0624003093Q004C6967687442617365026Q002E40026Q003440025Q0080464003043Q0042617365026Q00284003083Q004461726B42617365026Q001440026Q00184003043Q0054657874026Q006E4003083Q00436F2Q6C61707365026Q00644003063Q00436F726E657203073Q0050612Q64696E6703173Q005B4162792Q73616C5D205468656D6520612Q706C69656403183Q005B4162792Q73616C5D2057696E646F7720637265617465642Q033Q0054616203043Q00486F6D6503073Q0053656374696F6E03043Q00496E666F03053Q004C6162656C03253Q0048652Q6C6F2C207468616E6B20796F7520666F72207573696E67206D79207363726970742E03173Q004D616465206279204070746163756E6974202F2066616C03303Q00646D204070746163756E697420666F7220616E7920692Q73756573202F2062756773202F2073752Q67657374696F6E7303083Q00496E7465726E616C03093Q00436F2Q6C617073656403113Q00506572666F726D616E636520537461747303063Q004D656D6F7279030A3Q004D656D6F72793A202Q2D2Q033Q0043505503073Q004350553A202Q2D2Q033Q0047505503073Q004750553A202Q2D031A3Q005B4162792Q73616C5D20486F6D6520746162206372656174656403043Q007461736B03053Q00737061776E03073Q004661726D696E6703093Q004175746F204661726D03253Q005B4162792Q73616C5D204661726D696E67207461622F73656374696F6E206372656174656403083Q00436865636B626F7803063Q00456E61626C6503073Q0044656661756C74010003073Q004B657962696E64030F3Q00546F2Q676C65204175746F6661726D2Q033Q004B657903043Q00456E756D03073Q004B6579436F646503013Q005003053Q00706169727303053Q007461626C6503063Q00696E73657274031C3Q005B4162792Q73616C5D204C6F636174696F6E2063686F696365733A2003063Q00636F6E63617403023Q002C2003083Q0044726F70646F776E03093Q004661726D204172656103073Q004F7074696F6E7303063Q00536C6964657203103Q004F787967656E205468726573686F6C642Q033Q004D696E2Q033Q004D617803043Q005374657003063Q0053752Q66697803013Q002503153Q004F787967656E205761726E696E672042752Q666572026Q00F03F03273Q005B4162792Q73616C5D204661726D696E672073656374696F6E207769646765747320612Q64656403053Q00437570696403063Q004C6F6E656C7903053Q005368696E7903043Q00502Q6F7003043Q00526F636B03053Q00436F72616C03043Q004D6F2Q7303053Q004D6574616C03043Q0053616E6403063Q00416C62696E6F030B3Q005472616E73706172656E7403063Q0043616374757303063Q0053706972697403063Q00466F2Q73696C03063Q00476F6C64656E03083Q004E6567617469766503053Q00466169727903093Q00496E76697369626C6503043Q004E656F6E030B3Q00556C74726176696F6C657403063Q00522Q6F74656403063Q00536861646F7703073Q00416E67656C696303073Q004162792Q73616C03083Q0047726F756E64656403063Q0042616E616E6103043Q004A61646503063Q004C6971756964030B3Q00466973682046696C74657203283Q0053656C656374206D75746174696F6E7320746F207461726765742028656D707479203D20612Q6C29030D3Q004D756C746944726F70646F776E03093Q004D75746174696F6E7303293Q0053656C656374206669736820747970657320746F207461726765742028656D707479203D20612Q6C29030C3Q00466973682054797065732031030D3Q00416E6369656E7420536861726B030A3Q00416E676C65726669736803093Q0042612Q726163756461030C3Q004269676D6F75746866697368030D3Q00426C61636B66696E2054756E6103083Q00426C6F626669736803093Q00426C75652054616E67030C3Q00426C756566696E2054756E6103083Q00436176656669736803093Q00436C6F776E666973682Q033Q00436F6403063Q00446973637573030A3Q00447261676F6E6669736803073Q004579656669736803073Q0047726F75706572030C3Q0048612Q6D657220536861726B03133Q00496E666C617465642050752Q66657266697368030C3Q004A616775617220536861726B03093Q004A652Q6C7966697368030F3Q004B696E6720416E676C65726669736803083Q004C696F6E6669736803093Q004D616869204D616869030C3Q00466973682054797065732032030A3Q004D6F736173617572757303083Q004E61706F6C656F6E03073Q004E61727768616C030F3Q00506163696669632046616E66697368030B3Q0050656C6963616E2045656C03073Q00506972616E686103073Q00506F6D70616E6F030A3Q0050752Q66657266697368030D3Q005361636162616D62617370697303083Q005361696C6669736803063Q0053616C6D6F6E030C3Q0053636F7270696F6E6669736803093Q0053656120486F727365030A3Q0053656120547572746C6503053Q00536861726B03053Q00537175696403073Q0053756E6669736803083Q0054616D626171756903043Q0054616E67030B3Q00546F7563616E204669736803053Q0054726F757403053Q005768616C65030D3Q0052657365742046696C7465727303063Q0042752Q746F6E03233Q005B4162792Q73616C5D20466973682066696C7465722073656374696F6E20612Q646564032C3Q004661726D2053652Q74696E6773205B44616E6765726F75732C204564697420776974682043617574696F6E5D032D3Q0074772Q656E4475726174696F6E202D205365636F6E647320746F20436F6D706C65746520416E696D6174696F6E030E3Q0054772Q656E204475726174696F6E026Q00E03F03013Q007303153Q00526573657420746F2044656661756C74202833732903313Q007265747265617453702Q65644D756C7469706C696572202D204D756C7469706C69657320526574726561742053702Q656403133Q00526574726561742053702Q6564204D756C746903013Q007803153Q00526573657420746F2044656661756C74202832782903203Q006D696E44697374202D20466973682053682Q6F74696E672044697374616E6365030C3Q004D696E2044697374616E6365026Q00444003063Q00207374756473031B3Q00526573657420746F2044656661756C74202832352073747564732903233Q0074772Q656E5374657073202D20506F736974696F6E2055706461746520416D6F756E74030B3Q0054772Q656E20537465707303153Q00526573657420746F2044656661756C74202833302903283Q005B4162792Q73616C5D20416476616E6365642073656374696F6E207769646765747320612Q64656403083Q0054656C65706F727403093Q004C6F636174696F6E7303263Q005B4162792Q73616C5D2054656C65706F7274207461622F73656374696F6E206372656174656403213Q005B4162792Q73616C5D20412Q6465642074656C65706F72742062752Q746F6E3A2003043Q004D69736303093Q005574696C697469657303213Q00546869732069732061206E6F636C697020616E7469636865617420627970612Q7303223Q00596F752077692Q6C206861766520746F2072656A6F696E20746F2064697361626C6503283Q005468657265666F726520796F752063612Q6E6F7420746F756368206C616E64206E6F722073652Q6C030E3Q00456E61626C65204E6F2D636C6970031A3Q005B4162792Q73616C5D204D69736320746162206372656174656403083Q0053652Q74696E6773030D3Q004D61696E2053652Q74696E6773030A3Q00546F2Q676C652047554903013Q004C031E3Q005B4162792Q73616C5D2053652Q74696E677320746162206372656174656403193Q005B4162792Q73616C5D2055492066752Q6C79206C6F61646564031E3Q005B4162792Q73616C5D20412Q6C2073797374656D73206C61756E6368656400FF022Q0012073Q00013Q00204E5Q0002001235000200034Q006F3Q0002000200204800013Q0004001207000200013Q00204E000200020002001235000400054Q006F000200040002001207000300063Q001235000400074Q00520003000200012Q007900033Q0004001207000400093Q00204800040004000A0012350005000B3Q0012350006000C3Q0012350007000D4Q006F00040007000200103C000300080004001207000400093Q00204800040004000A0012350005000F3Q001235000600103Q001235000700114Q006F00040007000200103C0003000E0004001207000400093Q00204800040004000A001235000500133Q001235000600143Q001235000700154Q006F00040007000200103C000300120004001207000400093Q00204800040004000A001235000500173Q001235000600183Q001235000700194Q006F00040007000200103C000300160004001235000400084Q0064000500030004001207000600063Q0012350007001A4Q002C000800044Q00650007000700082Q00520006000200012Q001A00065Q0012350007001B3Q0012350008001C3Q0012350009001D4Q001A000A6Q001A000B6Q002B000C000C4Q0079000D5Q001235000E001E3Q001235000F001F3Q001235001000203Q001235001100214Q00010012000E00112Q007900136Q007900146Q007900156Q007900165Q001207001700063Q001235001800224Q0052001700020001001207001700063Q001235001800234Q002C001900084Q00650018001800192Q0052001700020001001207001700063Q001235001800244Q002C0019000E4Q00650018001800192Q0052001700020001001207001700063Q001235001800254Q002C001900104Q00650018001800192Q00520017000200012Q007900176Q007900186Q007900195Q000618001A3Q000100042Q006B3Q00184Q006B3Q00194Q006B3Q00134Q006B3Q00143Q000618001B0001000100052Q006B3Q00134Q006B3Q00144Q006B3Q00174Q006B3Q00184Q006B3Q00193Q000240001C00023Q000618001D0003000100012Q006B3Q00013Q001207001E00063Q001235001F00264Q0052001E00020001000618001E0004000100082Q006B3Q000B4Q006B3Q00014Q006B3Q00114Q006B3Q00124Q006B3Q001C4Q006B3Q00064Q006B3Q000D4Q006B3Q001D3Q000618001F0005000100032Q006B3Q00014Q006B3Q001C4Q006B3Q001D3Q001207002000063Q001235002100274Q0052002000020001001207002000063Q001235002100284Q0052002000020001001207002000293Q001207002100013Q00204E00210021002A0012350023002B4Q001E002100234Q004200203Q00022Q0081002000010001001207002000063Q0012350021002C3Q0012070022002D3Q0012070023002E4Q00320022000200022Q00650021002100222Q00520020000200010012070020002F3Q001235002100303Q001235002200313Q0012350023001D4Q003D0020002300010012070020002E3Q00204E0020002000322Q007900223Q0003003036002200330034001207002300363Q00204800230023000A001235002400373Q001235002500384Q006F00230025000200103C00220035002300303600220039003A2Q006F00200022000200204800210020003B00204800210021003C0012070022003E3Q00204800220022003F001235002300403Q001235002400413Q001235002500424Q006F00220025000200103C0021003D002200204800210020003B00204800210021003C0012070022003E3Q00204800220022003F001235002300443Q001235002400453Q001235002500464Q006F00220025000200103C00210043002200204800210020003B00204800210021003C0012070022003E3Q00204800220022003F001235002300213Q001235002400483Q001235002500494Q006F00220025000200103C00210047002200204800210020003B00204800210021003C0012070022003E3Q00204800220022003F0012350023004B3Q0012350024004C3Q0012350025004D4Q006F00220025000200103C0021004A002200204800210020003B00204800210021003C0012070022003E3Q00204800220022003F0012350023001D3Q0012350024004F3Q001235002500214Q006F00220025000200103C0021004E002200204800210020003B00204800210021003C0012070022003E3Q00204800220022003F001235002300513Q001235002400523Q0012350025004C4Q006F00220025000200103C00210050002200204800210020003B00204800210021003C0012070022003E3Q00204800220022003F001235002300463Q001235002400543Q001235002500424Q006F00220025000200103C00210053002200204800210020003B00204800210021003C0012070022003E3Q00204800220022003F001235002300563Q001235002400413Q001235002500424Q006F00220025000200103C00210055002200204800210020003B00204800210021003C00303600210057005100204800210020003B00204800210021003C003036002100580052001207002100063Q001235002200594Q0052002100020001001207002100063Q0012350022005A4Q005200210002000100204E00210020005B2Q007900233Q000100303600230033005C2Q006F00210023000200204E00220021005D2Q007900243Q000100303600240033005E2Q006F00220024000200204E00230022005F2Q007900253Q00010030360025003300602Q003D00230025000100204E00230022005F2Q007900253Q00010030360025003300612Q003D00230025000100204E00230022005F2Q007900253Q00010030360025003300622Q003D00230025000100204800230022006300303600230064003A00204E00230021005D2Q007900253Q00010030360025003300652Q006F00230025000200204800240023006300303600240064003A2Q007900243Q000300204E00250023005F2Q007900273Q00010030360027003300672Q006F00250027000200103C00240066002500204E00250023005F2Q007900273Q00010030360027003300692Q006F00250027000200103C00240068002500204E00250023005F2Q007900273Q000100303600270033006B2Q006F00250027000200103C0024006A0025001207002500063Q0012350026006C4Q00520025000200010012070025006D3Q00204800250025006E00061800260006000100022Q006B3Q00204Q006B3Q00244Q005200250002000100204E00250020005B2Q007900273Q000100303600270033006F2Q006F00250027000200204E00260025005D2Q007900283Q00010030360028003300702Q006F002600280002001207002700063Q001235002800714Q005200270002000100204E0027002600722Q007900293Q0002003036002900330073003036002900740075000618002A0007000100062Q006B3Q00064Q006B3Q00014Q006B3Q001D4Q006B3Q001C4Q006B3Q000B4Q006B3Q000C4Q003D0027002A000100204E0027002600762Q007900293Q0002003036002900330077001207002A00793Q002048002A002A007A002048002A002A007B00103C00290078002A000618002A0008000100062Q006B3Q00064Q006B3Q00014Q006B3Q001D4Q006B3Q001C4Q006B3Q000B4Q006B3Q000C3Q000240002B00094Q003D0027002B00012Q007900275Q0012070028007C4Q002C002900034Q002600280002002A00040E3Q00532Q01001207002D007D3Q002048002D002D007E2Q002C002E00274Q002C002F002B4Q003D002D002F00010006600028004E2Q01000200040E3Q004E2Q01001207002800063Q0012350029007F3Q001207002A007D3Q002048002A002A00802Q002C002B00273Q001235002C00814Q006F002A002C00022Q006500290029002A2Q005200280002000100204E0028002600822Q0079002A3Q0003003036002A0033008300103C002A0084002700103C002A00740004000618002B000A000100032Q006B3Q00044Q006B3Q00054Q006B3Q00034Q003D0028002B000100204E0028002600852Q0079002A3Q0006003036002A00330086003036002A0087001D003036002A00880040003036002A0089005100103C002A00740008003036002A008A008B000618002B000B000100012Q006B3Q00084Q003D0028002B000100204E0028002600852Q0079002A3Q0006003036002A0033008C003036002A0087001B003036002A0088004C003036002A0089008D003036002A0074001D003036002A008A008B000618002B000C000100012Q006B3Q00094Q003D0028002B0001001207002800063Q0012350029008E4Q00520028000200012Q0079002800163Q0012350029008F3Q001235002A00903Q001235002B00913Q001235002C00923Q001235002D00933Q001235002E00943Q001235002F00953Q001235003000963Q001235003100973Q001235003200983Q001235003300993Q0012350034009A3Q0012350035009B3Q0012350036009C3Q0012350037009D3Q0012350038009E3Q0012350039009F3Q001235003A00A03Q001235003B00A13Q001235003C00A23Q001235003D00A33Q001235003E00A43Q001235003F00A53Q001235004000A63Q001235004100A73Q001235004200A83Q001235004300A93Q001235004400AA4Q00150028001C00012Q002B0029002B3Q00204E002C0025005D2Q0079002E3Q0001003036002E003300AB2Q006F002C002E000200204E002D002C005F2Q0079002F3Q0001003036002F003300AC2Q003D002D002F000100204E002D002C00AD2Q0079002F3Q0003003036002F003300AE00103C002F008400282Q007900305Q00103C002F007400300006180030000D000100032Q006B3Q00134Q006B3Q001A4Q006B3Q00174Q006F002D003000022Q002C0029002D3Q00204E002D002C005F2Q0079002F3Q0001003036002F003300AF2Q003D002D002F000100204E002D002C00AD2Q0079002F3Q0003003036002F003300B02Q0079003000133Q001235003100B13Q001235003200B23Q001235003300B33Q001235003400B43Q001235003500B53Q001235003600B63Q001235003700B73Q001235003800B83Q001235003900B93Q001235003A00BA3Q001235003B00BB3Q001235003C00BC3Q001235003D00BD3Q001235003E00BE3Q001235003F00BF3Q001235004000C03Q001235004100C13Q001235004200C23Q001235004300C33Q001235004400C43Q001235004500C53Q001235004600C64Q001500300016000100103C002F008400302Q007900305Q00103C002F007400300006180030000E000100052Q006B3Q00154Q006B3Q00164Q006B3Q00144Q006B3Q001A4Q006B3Q00174Q006F002D003000022Q002C002A002D3Q00204E002D002C00AD2Q0079002F3Q0003003036002F003300C72Q0079003000133Q001235003100C83Q001235003200C93Q001235003300CA3Q001235003400CB3Q001235003500CC3Q001235003600CD3Q001235003700CE3Q001235003800CF3Q001235003900D03Q001235003A00D13Q001235003B00D23Q001235003C00D33Q001235003D00D43Q001235003E00D53Q001235003F00D63Q001235004000D73Q001235004100D83Q001235004200D93Q001235004300DA3Q001235004400DB3Q001235004500DC3Q001235004600DD4Q001500300016000100103C002F008400302Q007900305Q00103C002F007400300006180030000F000100052Q006B3Q00164Q006B3Q00154Q006B3Q00144Q006B3Q001A4Q006B3Q00174Q006F002D003000022Q002C002B002D3Q00204E002D002C005F2Q0079002F3Q0001003036002F003300DE2Q003D002D002F000100204E002D002C00DF2Q0079002F3Q0001003036002F003300DE00061800300010000100092Q006B3Q00134Q006B3Q00154Q006B3Q00164Q006B3Q00144Q006B3Q00294Q006B3Q002A4Q006B3Q002B4Q006B3Q001A4Q006B3Q00174Q003D002D00300001001207002D00063Q001235002E00E04Q0052002D0002000100204E002D0025005D2Q0079002F3Q0001003036002F003300E12Q006F002D002F000200204E002E002D005F2Q007900303Q00010030360030003300E22Q003D002E0030000100204E002E002D00852Q007900303Q00060030360030003300E300303600300087008D00303600300088001D0030360030008900E400303600300074001E0030360030008A00E500061800310011000100032Q006B3Q000E4Q006B3Q00124Q006B3Q00114Q006F002E0031000200204E002F002D00DF2Q007900313Q00010030360031003300E600061800320012000100012Q006B3Q002E4Q003D002F0032000100204E002F002D005F2Q007900313Q00010030360031003300E72Q003D002F0031000100204E002F002D00852Q007900313Q00060030360031003300E800303600310087008D0030360031008800510030360031008900E400303600310074001F0030360031008A00E900061800320013000100012Q006B3Q000F4Q006F002F0032000200204E0030002D00DF2Q007900323Q00010030360032003300EA00061800330014000100012Q006B3Q002F4Q003D00300033000100204E0030002D005F2Q007900323Q00010030360032003300EB2Q003D00300032000100204E0030002D00852Q007900323Q00060030360032003300EC0030360032008700510030360032008800400030360032008900510030360032007400ED0030360032008A00EE00061800330015000100012Q006B3Q00104Q006F00300033000200204E0031002D00DF2Q007900333Q00010030360033003300EF00061800340016000100012Q006B3Q00304Q003D00310034000100204E0031002D005F2Q007900333Q00010030360033003300F02Q003D00310033000100204E0031002D00852Q007900333Q00050030360033003300F100303600330087001D00303600330088004000303600330089005100303600330074002100061800340017000100032Q006B3Q00114Q006B3Q00124Q006B3Q000E4Q006F00310034000200204E0032002D00DF2Q007900343Q00010030360034003300F200061800350018000100012Q006B3Q00314Q003D003200350001001207003200063Q001235003300F34Q005200320002000100204E00320020005B2Q007900343Q00010030360034003300F42Q006F00320034000200204E00330032005D2Q007900353Q00010030360035003300F52Q006F003300350002001207003400063Q001235003500F64Q00520034000200010012070034007C4Q002C003500034Q002600340002003600040E3Q0094020100204E0039003300DF2Q0079003B3Q000100103C003B00330037000618003C0019000100032Q006B3Q00374Q006B3Q001F4Q006B3Q00384Q003D0039003C0001001207003900063Q001235003A00F74Q002C003B00374Q0065003A003A003B2Q00520039000200012Q007D00375Q000660003400860201000200040E3Q0086020100204E00340020005B2Q007900363Q00010030360036003300F82Q006F00340036000200204E00350034005D2Q007900373Q00010030360037003300F92Q006F00350037000200204E00360035005F2Q007900383Q00010030360038003300FA2Q003D00360038000100204E00360035005F2Q007900383Q00010030360038003300FB2Q003D00360038000100204E00360035005F2Q007900383Q00010030360038003300FC2Q003D00360038000100204E0036003500DF2Q007900383Q00010030360038003300FD0006180039001A000100012Q006B3Q00014Q003D003600390001001207003600063Q001235003700FE4Q005200360002000100204E00360020005B2Q007900383Q00010030360038003300FF2Q006F00360038000200204E00370036005D2Q007900393Q0001003036003900332Q0001006F00370039000200204E0038003700762Q0079003A3Q0002001235003B002Q012Q00103C003A0033003B001207003B00793Q002048003B003B007A001235003C0002013Q0064003B003B003C00103C003A0078003B000618003B001B000100012Q006B3Q00203Q000240003C001C4Q003D0038003C0001001207003800063Q00123500390003013Q0052003800020001001207003800063Q00123500390004013Q00520038000200010012070038006D3Q00204800380038006E0006180039001D000100092Q006B3Q00064Q006B3Q000A4Q006B3Q00014Q006B3Q000D4Q006B3Q001B4Q006B3Q00074Q006B3Q00084Q006B3Q00094Q006B3Q000C4Q00520038000200010012070038006D3Q00204800380038006E0006180039001E000100042Q006B3Q00064Q006B3Q000C4Q006B3Q000A4Q006B3Q00014Q00520038000200010012070038006D3Q00204800380038006E0006180039001F000100022Q006B3Q00064Q006B3Q00014Q00520038000200010012070038006D3Q00204800380038006E000618003900200001000E2Q006B3Q00064Q006B3Q000B4Q006B3Q00014Q006B3Q00074Q006B3Q00084Q006B3Q000A4Q006B3Q000C4Q006B3Q001E4Q006B3Q00054Q006B3Q00124Q006B3Q000F4Q006B3Q00174Q006B3Q00094Q006B3Q00104Q0052003800020001001207003800063Q00123500390005013Q00520038000200012Q00143Q00013Q00213Q00023Q0003063Q006970616972732Q0100154Q00798Q00688Q00798Q00683Q00013Q0012073Q00014Q0004000100024Q00263Q0002000200040E3Q000A00012Q000400055Q0020760005000400020006603Q00080001000200040E3Q000800010012073Q00014Q0004000100034Q00263Q0002000200040E3Q001200012Q0004000500013Q0020760005000400020006603Q00100001000200040E3Q001000012Q00143Q00017Q000D3Q00028Q00030E3Q0046696E6446697273744368696C6403043Q004865616403083Q00522Q6F7450617274010003053Q00737461747303043Q004669736803083Q004D75746174696F6E03053Q004C6162656C03083Q00666973685479706503043Q0054657874030C3Q00666973684D75746174696F6E3Q01634Q000400016Q0051000100013Q000E78000100050001000100040E3Q000500012Q001700016Q001A000100014Q0004000200014Q0051000200023Q000E780001000B0001000200040E3Q000B00012Q001700026Q001A000200013Q000655000100120001000100040E3Q00120001000655000200120001000100040E3Q001200012Q001A000300014Q0010000300024Q0004000300024Q0064000300033Q000655000300480001000100040E3Q0048000100204E00043Q0002001235000600034Q006F0004000600020006550004001E0001000100040E3Q001E000100204E00043Q0002001235000600044Q006F000400060002000655000400240001000100040E3Q002400012Q0004000500023Q00207600053Q00052Q001A00056Q0010000500023Q00204E000500040002001235000700064Q006F0005000700020006550005002D0001000100040E3Q002D00012Q0004000600023Q00207600063Q00052Q001A00066Q0010000600023Q00204E000600050002001235000800074Q006F00060008000200204E000700050002001235000900084Q006F000700090002000605000800380001000700040E3Q0038000100204E000800070002001235000A00094Q006F0008000A000200066C0006003C00013Q00040E3Q003C0001000655000800400001000100040E3Q004000012Q0004000900023Q00207600093Q00052Q001A00096Q0010000900024Q007900093Q0002002048000A0006000B00103C0009000A000A002048000A0008000B00103C0009000C000A2Q002C000300094Q0004000900024Q005B00093Q000300263F0003004C0001000500040E3Q004C00012Q001A00046Q0010000400023Q00066C0001005400013Q00040E3Q005400012Q0004000400033Q00204800050003000C2Q0064000400040005002602000400540001000D00040E3Q005400012Q001700046Q001A000400013Q00066C0002005D00013Q00040E3Q005D00012Q0004000500043Q00204800060003000A2Q00640005000500060026020005005D0001000D00040E3Q005D00012Q001700056Q001A000500013Q000605000600610001000400040E3Q006100012Q002C000600054Q0010000600024Q00143Q00017Q00073Q0003063Q00747970656F6603083Q00496E7374616E636503063Q00697061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103083Q004261736550617274030A3Q0043616E436F2Q6C696465021B3Q00066C3Q000700013Q00040E3Q00070001001207000200014Q002C00036Q0032000200020002002602000200080001000200040E3Q000800012Q00143Q00013Q001207000200033Q00204E00033Q00042Q0009000300044Q005800023Q000400040E3Q00180001001207000700014Q002C000800064Q003200070002000200263F000700180001000200040E3Q0018000100204E000700060005001235000900064Q006F00070009000200066C0007001800013Q00040E3Q0018000100103C0006000700010006600002000D0001000200040E3Q000D00012Q00143Q00017Q00073Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403163Q00412Q73656D626C794C696E65617256656C6F6369747903073Q00566563746F72332Q033Q006E6577028Q0001143Q0006500001000400013Q00040E3Q000400012Q000400015Q002048000100010001000655000100070001000100040E3Q000700012Q00143Q00013Q00204E000200010002001235000400034Q006F00020004000200066C0002001300013Q00040E3Q00130001001207000300053Q002048000300030006001235000400073Q001235000500073Q001235000600074Q006F00030006000200103C0002000400032Q00143Q00017Q00313Q0003063Q00506172656E7403043Q007761726E03343Q005B4162792Q73616C5D20736D2Q6F74684D6F7665546F3A20722Q6F74206973206E696C206F7220686173206E6F20706172656E7403093Q0043686172616374657203083Q00506F736974696F6E028Q0003053Q007072696E74032A3Q005B4162792Q73616C5D20736D2Q6F74684D6F7665546F2073746172746564202D3E207461726765743A2003083Q00746F737472696E67030A3Q00207C2073746570733A20026Q00F03F032B3Q005B4162792Q73616C5D20736D2Q6F74684D6F7665546F20696E74652Q727570746564206174207374657020033D3Q005B4162792Q73616C5D20736D2Q6F74684D6F7665546F3A2064657374506F73206F722063752Q72656E74506F73206973206E696C206174207374657020027Q004003063Q00747970656F6603073Q00566563746F723303093Q004D61676E6974756465026Q00244003063Q006E756D626572032B3Q005B4162792Q73616C5D20736D2Q6F74684D6F7665546F3A20737475636B20646574656374656420666F7220030E3Q00207C206D6F766564446973743A2003083Q00536166655A6F6E652Q0103173Q005B4162792Q73616C5D20426C61636B6C69737465643A2003063Q0020283135732903043Q007461736B03053Q0064656C6179026Q002E4003013Q005803013Q005903013Q005A03043Q006D61746803043Q007371727403333Q005B4162792Q73616C5D20736D2Q6F74684D6F7665546F3A2073746F7020636F6E646974696F6E206D657420617420646973742003053Q00666C2Q6F7203053Q0020666F72202Q033Q006E657703093Q00776F726B737061636503043Q0047616D6503053Q005475626573030E3Q0046696E6446697273744368696C6403043Q004E616D6503083Q00522Q6F7450617274025Q00804640026Q00144003053Q007063612Q6C030B3Q006D6F75736531636C69636B03043Q007761697403233Q005B4162792Q73616C5D20736D2Q6F74684D6F7665546F2066696E6973686564202D3E2006EF3Q00066C3Q000500013Q00040E3Q0005000100204800063Q00010006550006000B0001000100040E3Q000B0001001207000600023Q001235000700034Q00520006000200012Q001A00066Q006800066Q00143Q00014Q0004000600013Q002048000600060004000650000700100001000300040E3Q001000012Q0004000700023Q000650000800130001000400040E3Q001300012Q0004000800033Q00204800093Q0005001235000A00063Q001207000B00073Q001235000C00083Q001207000D00094Q002C000E00054Q0032000D00020002001235000E000A4Q002C000F00074Q0065000C000C000F2Q0052000B000200012Q001A000B00014Q0068000B6Q0004000B00044Q002C000C00064Q001A000D6Q003D000B000D0001001235000B000B4Q002C000C00073Q001235000D000B3Q00041F000B00DC00012Q0004000F00053Q00066C000F002E00013Q00040E3Q002E00012Q0004000F5Q000655000F00340001000100040E3Q00340001001207000F00073Q0012350010000C4Q002C0011000E4Q00650010001000112Q0052000F0002000100040E3Q00DC00012Q002C000F00014Q0062000F0001000200204800103Q000500066C000F003B00013Q00040E3Q003B0001000655001000410001000100040E3Q00410001001207001100023Q0012350012000D4Q002C0013000E4Q00650012001200132Q005200110002000100040E3Q00DC00012Q0053000A000A0008000E2E000E00790001000A00040E3Q00790001001235001100063Q0012070012000F4Q002C001300104Q003200120002000200263F001200520001001000040E3Q005200010012070012000F4Q002C001300094Q003200120002000200263F001200520001001000040E3Q005200012Q007500120010000900204800110012001100040E3Q00530001001235001100123Q0012070012000F4Q002C001300114Q003200120002000200263F001200770001001300040E3Q0077000100260D001100770001000B00040E3Q00770001001207001200023Q001235001300143Q001207001400094Q002C001500054Q0032001400020002001235001500154Q002C001600114Q00650013001300162Q005200120002000100066C000500DC00013Q00040E3Q00DC0001002602000500DC0001001600040E3Q00DC00012Q0004001200063Q002076001200050017001207001200073Q001235001300184Q002C001400053Q001235001500194Q00650013001300152Q00520012000200010012070012001A3Q00204800120012001B0012350013001C3Q00061800143Q000100022Q00163Q00064Q006B3Q00054Q003D00120014000100040E3Q00DC00012Q002C000900103Q001235000A00063Q0020480011000F001D00204800120010001D2Q00750011001100120020480012000F001E00204800130010001E2Q00750012001200130020480013000F001F00204800140010001F2Q0075001300130014001207001400203Q0020480014001400212Q00080015001100112Q00080016001200122Q00530015001500162Q00080016001300132Q00530015001500162Q003200140002000200066C0002009E00013Q00040E3Q009E00012Q002C001500024Q002C001600144Q003200150002000200066C0015009E00013Q00040E3Q009E0001001207001500073Q001235001600223Q001207001700203Q0020480017001700232Q002C001800144Q0032001700020002001235001800243Q001207001900094Q002C001A00054Q00320019000200022Q00650016001600192Q005200150002000100040E3Q00DC00012Q007500150007000E00203400150015000B00104A0015000B0015001207001600103Q00204800160016002500204800170010001D0020480018000F001D00204800190010001D2Q00750018001800192Q00080018001800152Q005300170017001800204800180010001E0020480019000F001E002048001A0010001E2Q007500190019001A2Q00080019001900152Q005300180018001900204800190010001F002048001A000F001F002048001B0010001F2Q0075001A001A001B2Q0008001A001A00152Q005300190019001A2Q006F0016001900022Q0004001700074Q002C001800064Q005200170002000100103C3Q00050016001207001700263Q00204800170017002700204800170017002800204E0017001700292Q0004001900013Q00204800190019002A2Q006F00170019000200066C001700CA00013Q00040E3Q00CA000100204E001800170029001235001A002B4Q006F0018001A000200066C001800CA00013Q00040E3Q00CA000100204800180017002B00103C001800050016001207001800203Q0020480018001800212Q00080019001100112Q0008001A001300132Q005300190019001A2Q003200180002000200260D001400D70001002C00040E3Q00D70001000E63002D00D70001001800040E3Q00D700010012070019002E3Q001207001A002F4Q00520019000200010012070019001A3Q0020480019001900302Q002C001A00084Q005200190002000100043B000B00280001001207000B00073Q001235000C00313Q001207000D00094Q002C000E00054Q0032000D000200022Q0065000C000C000D2Q0052000B000200012Q0004000B00074Q0004000C00013Q002048000C000C00042Q0052000B000200012Q0004000B00044Q0004000C00013Q002048000C000C00042Q001A000D00014Q003D000B000D00012Q001A000B6Q0068000B6Q00143Q00013Q00013Q00034Q0003053Q007072696E7403193Q005B4162792Q73616C5D20556E626C61636B6C69737465643A2000094Q00048Q0004000100013Q0020763Q000100010012073Q00023Q001235000100034Q0004000200014Q00650001000100022Q00523Q000200012Q00143Q00017Q001D3Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403043Q007761726E03303Q005B4162792Q73616C5D2074656C65706F7274546F3A2048756D616E6F6964522Q6F7450617274206E6F7420666F756E6403053Q007072696E74031A3Q005B4162792Q73616C5D2054656C65706F7274696E6720746F3A2003083Q00506F736974696F6E03013Q005803013Q005903013Q005A03043Q006D61746803043Q0073717274026Q0008402Q033Q006D6178026Q00244003053Q00666C2Q6F7202FCA9F1D24D62903F026Q00F03F03073Q00566563746F72332Q033Q006E657703093Q00776F726B737061636503043Q0047616D6503053Q00547562657303043Q004E616D6503083Q00522Q6F745061727403043Q007461736B03043Q0077616974031D3Q005B4162792Q73616C5D2054656C65706F727420636F6D706C6574653A2002804Q000400025Q002048000200020001000605000300070001000200040E3Q0007000100204E000300020002001235000500034Q006F0003000500020006550003000D0001000100040E3Q000D0001001207000400043Q001235000500054Q00520004000200012Q00143Q00013Q001207000400063Q001235000500074Q002C000600014Q00650005000500062Q00520004000200012Q0004000400014Q002C000500024Q001A00066Q003D00040006000100204800040003000800204800053Q00090020480006000400092Q007500050005000600204800063Q000A00204800070004000A2Q007500060006000700204800073Q000B00204800080004000B2Q00750007000700080012070008000C3Q00204800080008000D2Q00080009000500052Q0008000A000600062Q005300090009000A2Q0008000A000700072Q005300090009000A2Q00320008000200020012350009000E3Q001207000A000C3Q002048000A000A000F001235000B00103Q001207000C000C3Q002048000C000C00112Q0001000D000800092Q0009000C000D4Q0042000A3Q0002001235000B00123Q001235000C00134Q002C000D000A3Q001235000E00133Q00041F000C006500012Q00010010000F000A001207001100143Q00204800110011001500204800120004000900204800133Q00090020480014000400092Q00750013001300142Q00080013001300102Q005300120012001300204800130004000A00204800143Q000A00204800150004000A2Q00750014001400152Q00080014001400102Q005300130013001400204800140004000B00204800153Q000B00204800160004000B2Q00750015001500162Q00080015001500102Q00530014001400152Q006F0011001400022Q0004001200024Q002C001300024Q005200120002000100103C000300080011001207001200163Q00204800120012001700204800120012001800204E0012001200022Q000400145Q0020480014001400192Q006F00120014000200066C0012006000013Q00040E3Q0060000100204E0013001200020012350015001A4Q006F00130015000200066C0013006000013Q00040E3Q0060000100204800130012001A00103C0013000800110012070013001B3Q00204800130013001C2Q002C0014000B4Q005200130002000100043B000C0036000100103C000300083Q001207000C00163Q002048000C000C0017002048000C000C001800204E000C000C00022Q0004000E5Q002048000E000E00192Q006F000C000E000200066C000C007600013Q00040E3Q0076000100204E000D000C0002001235000F001A4Q006F000D000F000200066C000D007600013Q00040E3Q00760001002048000D000C001A00103C000D00084Q0004000D00014Q002C000E00024Q001A000F00014Q003D000D000F0001001207000D00063Q001235000E001D4Q002C000F00014Q0065000E000E000F2Q0052000D000200012Q00143Q00017Q000F3Q0003053Q007072696E7403283Q005B4162792Q73616C5D20506572666F726D616E6365207374617473206C2Q6F70207374617274656403043Q0067616D65030A3Q004765745365727669636503053Q00537461747303103Q00506572666F726D616E6365537461747303053Q007061697273030B3Q004765744368696C6472656E03043Q004E616D6503083Q00496E7465726E616C03073Q0052752Q6E696E6703043Q007461736B03043Q0077616974026Q00F03F03053Q007063612Q6C00243Q0012073Q00013Q001235000100024Q00523Q000200010012073Q00033Q00204E5Q0004001235000200054Q006F3Q000200020020485Q00062Q007900015Q001207000200073Q00204E00033Q00082Q0009000300044Q005800023Q000400040E3Q001000010020480007000600092Q005B0001000700060006600002000E0001000200040E3Q000E000100061800023Q000100012Q006B3Q00014Q000400035Q00204800030003000A00204800030003000B00066C0003002300013Q00040E3Q002300010012070003000C3Q00204800030003000D0012350004000E4Q00520003000200010012070003000F3Q00061800040001000100022Q00163Q00014Q006B3Q00024Q005200030002000100040E3Q001400012Q00143Q00013Q00023Q00073Q002Q033Q004E2F4103073Q00412Q6472652Q73030B3Q006D656D6F72795F7265616403063Q00737472696E67026Q006A40028Q00026Q006B40011A4Q000400016Q0064000100013Q000655000100060001000100040E3Q00060001001235000200014Q0010000200023Q002048000200010002001207000300033Q001235000400043Q0020340005000200052Q006F00030005000200066C0003001100013Q00040E3Q001100012Q0051000400033Q000E63000600110001000400040E3Q001100012Q0010000300023Q001207000400033Q001235000500043Q0020340006000200072Q006F000400060002000650000500180001000400040E3Q00180001001235000500014Q0010000500024Q00143Q00017Q00073Q0003063Q004D656D6F72792Q033Q0053657403083Q004D656D6F72793A202Q033Q0043505503053Q004350553A202Q033Q0047505503053Q004750553A20001C4Q00047Q0020485Q000100204E5Q0002001235000200034Q0004000300013Q001235000400014Q00320003000200022Q00650002000200032Q003D3Q000200012Q00047Q0020485Q000400204E5Q0002001235000200054Q0004000300013Q001235000400044Q00320003000200022Q00650002000200032Q003D3Q000200012Q00047Q0020485Q000600204E5Q0002001235000200074Q0004000300013Q001235000400064Q00320003000200022Q00650002000200032Q003D3Q000200012Q00143Q00017Q00073Q0003053Q007072696E74031D3Q005B4162792Q73616C5D204175746F206661726D20746F2Q676C65643A2003083Q00746F737472696E6703093Q00436861726163746572030A3Q006B657972656C65617365025Q0040524003283Q005B4162792Q73616C5D204175746F206661726D2073746F2Q7065642C20737461746520726573657401214Q00687Q001207000100013Q001235000200023Q001207000300034Q002C00046Q00320003000200022Q00650002000200032Q00520001000200012Q000400015Q000655000100200001000100040E3Q002000012Q0004000100013Q00204800010001000400066C0001002000013Q00040E3Q00200001001207000100053Q001235000200064Q00520001000200012Q0004000100024Q00810001000100012Q0004000100034Q0004000200013Q0020480002000200042Q001A000300014Q003D0001000300012Q001A00016Q0068000100044Q002B000100014Q0068000100053Q001207000100013Q001235000200074Q00520001000200012Q00143Q00017Q00073Q0003053Q007072696E7403253Q005B4162792Q73616C5D204175746F206661726D206B657962696E6420746F2Q676C65643A2003083Q00746F737472696E6703093Q00436861726163746572030A3Q006B657972656C65617365025Q0040524003283Q005B4162792Q73616C5D204175746F206661726D2073746F2Q7065642C20737461746520726573657400234Q00048Q00578Q00687Q0012073Q00013Q001235000100023Q001207000200034Q000400036Q00320002000200022Q00650001000100022Q00523Q000200012Q00047Q0006553Q00220001000100040E3Q002200012Q00043Q00013Q0020485Q000400066C3Q002200013Q00040E3Q002200010012073Q00053Q001235000100064Q00523Q000200012Q00043Q00024Q00813Q000100012Q00043Q00034Q0004000100013Q0020480001000100042Q001A000200014Q003D3Q000200012Q001A8Q00683Q00044Q002B8Q00683Q00053Q0012073Q00013Q001235000100074Q00523Q000200012Q00143Q00017Q00033Q0003053Q007072696E7403273Q005B4162792Q73616C5D204175746F6661726D206B657962696E64206368616E67656420746F3A2003083Q00746F737472696E6701083Q001207000100013Q001235000200023Q001207000300034Q002C00046Q00320003000200022Q00650002000200032Q00520001000200012Q00143Q00017Q00043Q0003053Q007072696E7403203Q005B4162792Q73616C5D204661726D2061726561206368616E67656420746F3A2003083Q00207C20706F733A2003083Q00746F737472696E67010F4Q00688Q0004000100024Q000400026Q00640001000100022Q0068000100013Q001207000100013Q001235000200024Q000400035Q001235000400033Q001207000500044Q0004000600014Q00320005000200022Q00650002000200052Q00520001000200012Q00143Q00017Q00033Q0003053Q007072696E7403233Q005B4162792Q73616C5D204F787967656E207468726573686F6C642073657420746F3A2003013Q002501084Q00687Q001207000100013Q001235000200024Q002C00035Q001235000400034Q00650002000200042Q00520001000200012Q00143Q00017Q00033Q0003053Q007072696E7403283Q005B4162792Q73616C5D204F787967656E207761726E696E672062752Q6665722073657420746F3A2003013Q002501084Q00687Q001207000100013Q001235000200024Q002C00035Q001235000400034Q00650002000200042Q00520001000200012Q00143Q00017Q00073Q00028Q0003053Q007072696E74033B3Q005B4162792Q73616C5D204D75746174696F6E2066696C74657220636C6561726564202D20746172676574696E6720612Q6C206D75746174696F6E73031F3Q005B4162792Q73616C5D204D75746174696F6E2066696C746572207365743A2003053Q007461626C6503063Q00636F6E63617403023Q002C2001164Q00688Q0004000100014Q00810001000100012Q007900016Q0068000100024Q005100015Q00263F0001000C0001000100040E3Q000C0001001207000100023Q001235000200034Q005200010002000100040E3Q00150001001207000100023Q001235000200043Q001207000300053Q0020480003000300062Q002C00045Q001235000500074Q006F0003000500022Q00650002000200032Q00520001000200012Q00143Q00017Q00093Q0003063Q0069706169727303053Q007461626C6503063Q00696E73657274028Q0003053Q007072696E7403383Q005B4162792Q73616C5D204669736820747970652066696C74657220636C6561726564202D20746172676574696E6720612Q6C20747970657303203Q005B4162792Q73616C5D204669736820747970652066696C746572207365743A2003063Q00636F6E63617403023Q002C20012E4Q00688Q007900015Q001207000200014Q000400036Q002600020002000400040E3Q000B0001001207000700023Q0020480007000700032Q002C000800014Q002C000900064Q003D000700090001000660000200060001000200040E3Q00060001001207000200014Q0004000300014Q002600020002000400040E3Q00160001001207000700023Q0020480007000700032Q002C000800014Q002C000900064Q003D000700090001000660000200110001000200040E3Q001100012Q0068000100024Q0004000200034Q00810002000100012Q007900026Q0068000200044Q0051000200013Q00263F000200240001000400040E3Q00240001001207000200053Q001235000300064Q005200020002000100040E3Q002D0001001207000200053Q001235000300073Q001207000400023Q0020480004000400082Q002C000500013Q001235000600094Q006F0004000600022Q00650003000300042Q00520002000200012Q00143Q00017Q00093Q0003063Q0069706169727303053Q007461626C6503063Q00696E73657274028Q0003053Q007072696E7403383Q005B4162792Q73616C5D204669736820747970652066696C74657220636C6561726564202D20746172676574696E6720612Q6C20747970657303203Q005B4162792Q73616C5D204669736820747970652066696C746572207365743A2003063Q00636F6E63617403023Q002C20012E4Q00688Q007900015Q001207000200014Q0004000300014Q002600020002000400040E3Q000B0001001207000700023Q0020480007000700032Q002C000800014Q002C000900064Q003D000700090001000660000200060001000200040E3Q00060001001207000200014Q000400036Q002600020002000400040E3Q00160001001207000700023Q0020480007000700032Q002C000800014Q002C000900064Q003D000700090001000660000200110001000200040E3Q001100012Q0068000100024Q0004000200034Q00810002000100012Q007900026Q0068000200044Q0051000200013Q00263F000200240001000400040E3Q00240001001207000200053Q001235000300064Q005200020002000100040E3Q002D0001001207000200053Q001235000300073Q001207000400023Q0020480004000400082Q002C000500013Q001235000600094Q006F0004000600022Q00650003000300042Q00520002000200012Q00143Q00017Q00033Q002Q033Q0053657403053Q007072696E7403203Q005B4162792Q73616C5D20412Q6C20666973682066696C7465727320726573657400254Q00798Q00688Q00798Q00683Q00014Q00798Q00683Q00024Q00798Q00683Q00034Q00043Q00043Q00066C3Q000F00013Q00040E3Q000F00012Q00043Q00043Q00204E5Q00012Q007900026Q003D3Q000200012Q00043Q00053Q00066C3Q001600013Q00040E3Q001600012Q00043Q00053Q00204E5Q00012Q007900026Q003D3Q000200012Q00043Q00063Q00066C3Q001D00013Q00040E3Q001D00012Q00043Q00063Q00204E5Q00012Q007900026Q003D3Q000200012Q00043Q00074Q00813Q000100012Q00798Q00683Q00083Q0012073Q00023Q001235000100034Q00523Q000200012Q00143Q00017Q00023Q0003053Q007072696E7403203Q005B4162792Q73616C5D2074772Q656E4475726174696F6E2073657420746F3A20010B4Q00688Q000400016Q0004000200024Q00010001000100022Q0068000100013Q001207000100013Q001235000200024Q002C00036Q00650002000200032Q00520001000200012Q00143Q00017Q00043Q002Q033Q00536574026Q00084003053Q007072696E74032B3Q005B4162792Q73616C5D2074772Q656E4475726174696F6E20726573657420746F2064656661756C743A203300084Q00047Q00204E5Q0001001235000200024Q003D3Q000200010012073Q00033Q001235000100044Q00523Q000200012Q00143Q00017Q00023Q0003053Q007072696E7403293Q005B4162792Q73616C5D207265747265617453702Q65644D756C7469706C6965722073657420746F3A2001074Q00687Q001207000100013Q001235000200024Q002C00036Q00650002000200032Q00520001000200012Q00143Q00017Q00043Q002Q033Q00536574027Q004003053Q007072696E7403343Q005B4162792Q73616C5D207265747265617453702Q65644D756C7469706C69657220726573657420746F2064656661756C743A203200084Q00047Q00204E5Q0001001235000200024Q003D3Q000200010012073Q00033Q001235000100044Q00523Q000200012Q00143Q00017Q00023Q0003053Q007072696E74031A3Q005B4162792Q73616C5D206D696E446973742073657420746F3A2001074Q00687Q001207000100013Q001235000200024Q002C00036Q00650002000200032Q00520001000200012Q00143Q00017Q00043Q002Q033Q00536574026Q00444003053Q007072696E7403263Q005B4162792Q73616C5D206D696E4469737420726573657420746F2064656661756C743A20323500084Q00047Q00204E5Q0001001235000200024Q003D3Q000200010012073Q00033Q001235000100044Q00523Q000200012Q00143Q00017Q00023Q0003053Q007072696E74031D3Q005B4162792Q73616C5D2074772Q656E53746570732073657420746F3A20010B4Q00688Q0004000100024Q000400026Q00010001000100022Q0068000100013Q001207000100013Q001235000200024Q002C00036Q00650002000200032Q00520001000200012Q00143Q00017Q00043Q002Q033Q00536574026Q003E4003053Q007072696E7403293Q005B4162792Q73616C5D2074772Q656E537465707320726573657420746F2064656661756C743A20333000084Q00047Q00204E5Q0001001235000200024Q003D3Q000200010012073Q00033Q001235000100044Q00523Q000200012Q00143Q00017Q00043Q0003053Q007072696E7403233Q005B4162792Q73616C5D2054656C65706F72742062752Q746F6E207072652Q7365643A2003043Q007461736B03053Q00737061776E000D3Q0012073Q00013Q001235000100024Q000400026Q00650001000100022Q00523Q000200010012073Q00033Q0020485Q000400061800013Q000100032Q00163Q00014Q00163Q00024Q00168Q00523Q000200012Q00143Q00013Q00018Q00054Q00048Q0004000100014Q0004000200024Q003D3Q000200012Q00143Q00017Q00043Q0003053Q007072696E74031B3Q005B4162792Q73616C5D204E6F2D636C69702061637469766174656403043Q007461736B03053Q00737061776E00093Q0012073Q00013Q001235000100024Q00523Q000200010012073Q00033Q0020485Q000400061800013Q000100012Q00168Q00523Q000200012Q00143Q00013Q00013Q001B3Q0003093Q00776F726B7370616365030E3Q0046696E6446697273744368696C642Q033Q004D617003063Q00646562726973030E3Q0047657444657363656E64616E7473026Q00F03F2Q033Q0049734103083Q004261736550617274030A3Q0043616E436F2Q6C696465010003053Q007063612Q6C03063Q00506172656E74025Q00408F40028Q0003043Q007461736B03043Q007761697403043Q007761726E03203Q005B4162792Q73616C5D204E6F2D636C69703A204D6170206E6F7420666F756E6403093Q0043686172616374657203063Q0069706169727303053Q007072696E7403233Q005B4162792Q73616C5D204E6F2D636C69703A2048756D616E6F6964522Q6F745061727403043Q0047616D6503053Q00547562657303043Q004E616D6503173Q005B4162792Q73616C5D204E6F2D636C69703A205475626503193Q005B4162792Q73616C5D204E6F2D636C69703A204C6F61646564005D3Q0012073Q00013Q00204E5Q0002001235000200034Q006F3Q00020002001207000100013Q00204E000100010002001235000300044Q006F00010003000200066C3Q002700013Q00040E3Q0027000100066C0001002700013Q00040E3Q0027000100204E00023Q00052Q0032000200020002001235000300064Q0051000400023Q001235000500063Q00041F0003002600012Q006400070002000600204E000800070007001235000A00084Q006F0008000A000200066C0008001E00013Q00040E3Q001E000100303600070009000A0012070008000B3Q00061800093Q000100012Q006B3Q00074Q005200080002000100103C0007000C000100200A00080006000D00263F000800240001000E00040E3Q002400010012070008000F3Q0020480008000800102Q00810008000100012Q007D00075Q00043B00030012000100040E3Q002A0001001207000200113Q001235000300124Q00520002000200012Q000400025Q00204800020002001300066C0002004000013Q00040E3Q00400001001207000200144Q000400035Q00204800030003001300204E0003000300052Q0009000300044Q005800023Q000400040E3Q003B000100204E000700060007001235000900084Q006F00070009000200066C0007003B00013Q00040E3Q003B000100303600060009000A000660000200350001000200040E3Q00350001001207000200153Q001235000300164Q0052000200020001001207000200013Q00204800020002001700204800020002001800204E0002000200022Q000400045Q0020480004000400192Q006F00020004000200066C0002005900013Q00040E3Q00590001001207000300143Q00204E0004000200052Q0009000400054Q005800033Q000500040E3Q0054000100204E000800070007001235000A00084Q006F0008000A000200066C0008005400013Q00040E3Q0054000100303600070009000A0006600003004E0001000200040E3Q004E0001001207000300153Q0012350004001A4Q0052000300020001001207000300153Q0012350004001B4Q00520003000200012Q00143Q00013Q00013Q00033Q0003083Q0043616E5175657279010003083Q0043616E546F75636800054Q00047Q0030363Q000100022Q00047Q0030363Q000300022Q00143Q00017Q00033Q0003063Q00546F2Q676C6503053Q007072696E7403153Q005B4162792Q73616C5D2047554920746F2Q676C656400074Q00047Q00204E5Q00012Q00523Q000200010012073Q00023Q001235000100034Q00523Q000200012Q00143Q00017Q00033Q0003053Q007072696E7403223Q005B4162792Q73616C5D20475549206B657962696E64206368616E67656420746F3A2003083Q00746F737472696E6701083Q001207000100013Q001235000200023Q001207000300034Q002C00046Q00320003000200022Q00650002000200032Q00520001000200012Q00143Q00017Q00223Q0003053Q007072696E7403203Q005B4162792Q73616C5D2046697368207363616E206C2Q6F70207374617274656403043Q007461736B03043Q0077616974026Q00E03F03093Q00776F726B737061636503043Q0047616D6503043Q0046697368030E3Q0046696E6446697273744368696C6403063Q00636C69656E7403093Q0043686172616374657203103Q0048756D616E6F6964522Q6F745061727403083Q00506F736974696F6E024Q007E842E41028Q0003063Q00697061697273030B3Q004765744368696C6472656E026Q00F03F03043Q004E616D6503043Q004865616403083Q00522Q6F7450617274030B3Q005072696D6172795061727403013Q005803013Q005903013Q005A03043Q006D61746803043Q0073717274026Q003E4003053Q007063612Q6C03103Q005B4162792Q73616C5D205363616E3A2003093Q0020746F74616C207C20030F3Q0020626C61636B6C6973746564207C2003143Q002066696C7465726564207C207461726765743A2003043Q006E6F6E6500953Q0012073Q00013Q001235000100024Q00523Q000200010012073Q00033Q0020485Q0004001235000100054Q00523Q000200012Q00047Q00066C3Q000300013Q00040E3Q000300012Q00043Q00013Q00066C3Q000E00013Q00040E3Q000E000100040E3Q000300010012073Q00063Q0020485Q00070020485Q000800066C3Q001900013Q00040E3Q001900010012073Q00063Q0020485Q00070020485Q000800204E5Q00090012350002000A4Q006F3Q000200020006553Q001C0001000100040E3Q001C000100040E3Q000300012Q0004000100023Q00204800010001000B000605000200230001000100040E3Q0023000100204E0002000100090012350004000C4Q006F000200040002000655000200260001000100040E3Q0026000100040E3Q0003000100204800030002000D2Q002B000400043Q0012350005000E3Q0012350006000F3Q0012350007000F3Q0012350008000F3Q001207000900103Q00204E000A3Q00112Q0009000A000B4Q005800093Q000B00040E3Q006E00010020340006000600122Q0004000E00033Q002048000F000D00132Q0064000E000E000F00066C000E003900013Q00040E3Q0039000100203400070007001200040E3Q006800012Q0004000E00044Q002C000F000D4Q0032000E0002000200066C000E006700013Q00040E3Q0067000100204E000E000D0009001235001000144Q006F000E00100002000655000E00490001000100040E3Q0049000100204E000E000D0009001235001000154Q006F000E00100002000655000E00490001000100040E3Q00490001002048000E000D001600066C000E006800013Q00040E3Q00680001002048000F000E000D00066C000F006800013Q00040E3Q00680001002048000F000E000D002048000F000F00170020480010000300172Q0075000F000F00100020480010000E000D0020480010001000180020480011000300182Q00750010001000110020480011000E000D0020480011001100190020480012000300192Q00750011001100120012070012001A3Q00204800120012001B2Q00080013000F000F2Q00080014001000102Q00530013001300142Q00080014001100112Q00530013001300142Q003200120002000200061C001200680001000500040E3Q006800012Q002C000500124Q002C0004000D3Q00040E3Q0068000100203400080008001200200A000E0006001C00263F000E006E0001000F00040E3Q006E0001001207000E00033Q002048000E000E00042Q0081000E00010001000660000900310001000200040E3Q003100012Q001A00095Q001207000A001D3Q000618000B3Q000100052Q00163Q00024Q00163Q00054Q006B3Q00094Q00163Q00064Q00163Q00074Q0052000A000200010006550009007D0001000100040E3Q007D00012Q0068000400083Q00040E3Q007F00012Q002B000A000A4Q0068000A00083Q001207000A00013Q001235000B001E4Q002C000C00063Q001235000D001F4Q002C000E00073Q001235000F00204Q002C001000083Q001235001100213Q00066C0004008C00013Q00040E3Q008C00010020480012000400130006550012008D0001000100040E3Q008D0001001235001200224Q0065000B000B00122Q0052000A000200012Q007D7Q00040E3Q000300012Q007D7Q00040E3Q0003000100040E3Q000300012Q00143Q00013Q00013Q00093Q0003093Q00506C6179657247756903043Q004D61696E030E3Q0046696E6446697273744368696C6403063Q004F787967656E03083Q00746F6E756D626572030C3Q00476574412Q7472696275746503093Q006F6C646F787967656E026Q005940029Q00224Q00047Q0020485Q00010020485Q000200204E5Q0003001235000200044Q006F3Q0002000200066C3Q002100013Q00040E3Q00210001001207000100053Q00204E00023Q0006001235000400074Q001E000200044Q004200013Q0002000655000100100001000100040E3Q00100001001235000100084Q0004000200013Q000E63000900160001000200040E3Q001600012Q0004000200013Q000655000200170001000100040E3Q00170001001235000200084Q000100030001000200202A0003000300082Q0004000400034Q0004000500044Q0053000400040005000620000300020001000400040E3Q001F00012Q001700046Q001A000400014Q0068000400024Q00143Q00017Q00073Q0003053Q007072696E74031D3Q005B4162792Q73616C5D2043616D657261206C2Q6F702073746172746564028Q0003043Q007461736B03043Q0077616974029A5Q99A93F03053Q007063612Q6C00243Q0012073Q00013Q001235000100024Q00523Q000200010012353Q00033Q001207000100043Q002048000100010005001235000200064Q00520001000200012Q000400015Q00066C0001001400013Q00040E3Q001400012Q0004000100013Q00066C0001001400013Q00040E3Q001400010012353Q00033Q001207000100073Q00061800023Q000100012Q00163Q00014Q005200010002000100040E3Q000400012Q000400015Q00066C0001000400013Q00040E3Q000400012Q0004000100013Q000655000100040001000100040E3Q000400012Q0004000100023Q000655000100040001000100040E3Q00040001001207000100073Q00061800020001000100022Q00163Q00034Q006B8Q005200010002000100040E3Q000400012Q00143Q00013Q00023Q00083Q00030E3Q0046696E6446697273744368696C6403043Q004865616403083Q00522Q6F7450617274030B3Q005072696D6172795061727403093Q00776F726B7370616365030D3Q0043752Q72656E7443616D65726103063Q006C2Q6F6B417403083Q00506F736974696F6E00194Q00047Q00204E5Q0001001235000200024Q006F3Q000200020006553Q000E0001000100040E3Q000E00012Q00047Q00204E5Q0001001235000200034Q006F3Q000200020006553Q000E0001000100040E3Q000E00012Q00047Q0020485Q000400066C3Q001800013Q00040E3Q00180001001207000100053Q002048000100010006002048000100010007001207000200053Q00204800020002000600204800020002000800204800033Q00082Q003D0001000300012Q00143Q00017Q00113Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F7450617274026Q00F03F025Q0080764003043Q006D6174682Q033Q00726164026Q00344003083Q00506F736974696F6E03073Q00566563746F72332Q033Q006E65772Q033Q00636F73028Q002Q033Q0073696E03093Q00776F726B7370616365030D3Q0043752Q72656E7443616D65726103063Q006C2Q6F6B4174002C4Q00047Q0020485Q00010006050001000700013Q00040E3Q0007000100204E00013Q0002001235000300034Q006F0001000300020006550001000A0001000100040E3Q000A00012Q00143Q00014Q0004000200013Q00203400020002000400200A0002000200052Q0068000200013Q001207000200063Q0020480002000200072Q0004000300014Q0032000200020002001235000300083Q0020480004000100090012070005000A3Q00204800050005000B001207000600063Q00204800060006000C2Q002C000700024Q00320006000200022Q00080006000600030012350007000D3Q001207000800063Q00204800080008000E2Q002C000900024Q00320008000200022Q00080008000800032Q006F0005000800022Q00530004000400050012070005000F3Q0020480005000500100020480005000500110012070006000F3Q0020480006000600100020480006000600092Q002C000700044Q003D0005000700012Q00143Q00017Q00093Q0003053Q007072696E7403213Q005B4162792Q73616C5D204175746F2D6361746368206C2Q6F70207374617274656403043Q007461736B03043Q0077616974026Q00F03F03053Q007063612Q6C03043Q007761726E031C3Q005B4162792Q73616C5D204175746F2D636174636820652Q726F723A2003083Q00746F737472696E6700193Q0012073Q00013Q001235000100024Q00523Q000200010012073Q00033Q0020485Q0004001235000100054Q00523Q000200012Q00047Q00066C3Q000300013Q00040E3Q000300010012073Q00063Q00061800013Q000100012Q00163Q00014Q00263Q000200010006553Q00030001000100040E3Q00030001001207000200073Q001235000300083Q001207000400094Q002C000500014Q00320004000200022Q00650003000300042Q005200020002000100040E3Q000300012Q00143Q00013Q00013Q00133Q0003093Q00506C6179657247756903043Q004D61696E030B3Q004361746368696E6742617203053Q004672616D652Q033Q0042617203053Q00436174636803053Q0047722Q656E03073Q00412Q6472652Q73030C3Q006D656D6F72795F777269746503053Q00666C6F6174025Q00E09440026Q00F03F025Q00F09440026Q009540025Q0010954003053Q007072696E74032D3Q005B4162792Q73616C5D204175746F2D63617463683A206D656D6F7279207772692Q74656E20617420626173652003043Q007761726E03283Q005B4162792Q73616C5D204175746F2D63617463683A20636F6E74726F6C42617365206973206E696C00294Q00047Q0020485Q00010020485Q00020020485Q00030020485Q00040020485Q000500204800013Q000600204800010001000700204800010001000800066C0001002500013Q00040E3Q00250001001207000200093Q0012350003000A3Q00203400040001000B0012350005000C4Q003D000200050001001207000200093Q0012350003000A3Q00203400040001000D0012350005000C4Q003D000200050001001207000200093Q0012350003000A3Q00203400040001000E0012350005000C4Q003D000200050001001207000200093Q0012350003000A3Q00203400040001000F0012350005000C4Q003D000200050001001207000200103Q001235000300114Q002C000400014Q00650003000300042Q005200020002000100040E3Q00280001001207000200123Q001235000300134Q00520002000200012Q00143Q00017Q00413Q0003053Q007072696E74031C3Q005B4162792Q73616C5D204D61696E206379636C652073746172746564028Q0003043Q007461736B03043Q0077616974029A5Q99B93F03083Q006B65797072652Q73025Q0040524003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403043Q007761726E03303Q005B4162792Q73616C5D204D61696E206379636C653A2048756D616E6F6964522Q6F7450617274206E6F7420666F756E6403093Q00506C6179657247756903043Q004D61696E03063Q004F787967656E03293Q005B4162792Q73616C5D204D61696E206379636C653A204F787967656E205549206E6F7420666F756E6403083Q00746F6E756D626572030C3Q00476574412Q7472696275746503093Q006F6C646F787967656E026Q00594003163Q005B4162792Q73616C5D204E6577206D61784F78793A20027Q0040030F3Q005B4162792Q73616C5D204F78793A2003043Q006D61746803053Q00666C2Q6F7203013Q002F03023Q00202803103Q002529207C207468726573686F6C643A2003103Q0025207C2072657472656174696E673A2003083Q00746F737472696E6703353Q005B4162792Q73616C5D204C4F57204F585947454E2C2052657472656174696E6720746F2073616665207A6F6E65207C206F78793A2003013Q0025025Q00805840031B3Q005B4162792Q73616C5D204F787967656E20726573746F726564202803113Q0025292C20726573756D696E67206661726D03053Q00737061776E03093Q00776F726B737061636503043Q0047616D6503043Q004669736803063Q00636C69656E74033D3Q005B4162792Q73616C5D204669736820666F6C646572206E6F7420666F756E6420617420776F726B73706163652E47616D652E466973682E636C69656E7403063Q00506172656E7403043Q004E616D65010003083Q00666973685479706503013Q003F030C3Q00666973684D75746174696F6E03163Q005B4162792Q73616C5D204E6577207461726765743A2003013Q002903083Q00522Q6F745061727403043Q004865616403083Q00506F736974696F6E03013Q005803013Q005903013Q005A03043Q0073717274031A3Q005B4162792Q73616C5D204D6F76696E6720746F20666973683A2003093Q00207C20646973743A20026Q00144003233Q005B4162792Q73616C5D20496E2072616E67652C20636C69636B696E6720666973683A2003053Q007063612Q6C030B3Q006D6F75736531636C69636B00033F3Q005B4162792Q73616C5D204E6F2076616C696420746172676574206669736820666F756E64202866696C746572206D617920626520742Q6F20737472696374290025012Q0012073Q00013Q001235000100024Q00523Q000200012Q002B7Q001235000100033Q001207000200043Q002048000200020005001235000300064Q00520002000200012Q000400025Q00066C0002000500013Q00040E3Q000500012Q0004000200013Q00066C0002001000013Q00040E3Q0010000100040E3Q00050001001207000200073Q001235000300084Q00520002000200012Q0004000200023Q0020480002000200090006050003001A0001000200040E3Q001A000100204E00030002000A0012350005000B4Q006F000300050002000655000300200001000100040E3Q002000010012070004000C3Q0012350005000D4Q005200040002000100040E3Q000500012Q0004000400023Q00204800040004000E00204800040004000F00204E00040004000A001235000600104Q006F0004000600020006550004002B0001000100040E3Q002B00010012070005000C3Q001235000600114Q005200050002000100066C0004003400013Q00040E3Q00340001001207000500123Q00204E000600040013001235000800144Q001E000600084Q004200053Q0002000655000500350001000100040E3Q00350001001235000500154Q0004000600033Q00061C0006003E0001000500040E3Q003E00012Q0068000500033Q001207000600013Q001235000700164Q0004000800034Q00650007000700082Q00520006000200012Q0004000600033Q000E63000300440001000600040E3Q004400012Q0004000600033Q000655000600450001000100040E3Q00450001001235000600154Q000100070005000600202A000700070015002034000100010006000E2E001700600001000100040E3Q00600001001207000800013Q001235000900183Q001207000A00193Q002048000A000A001A2Q002C000B00054Q0032000A00020002001235000B001B4Q002C000C00063Q001235000D001C3Q001207000E00193Q002048000E000E001A2Q002C000F00074Q0032000E00020002001235000F001D4Q0004001000043Q0012350011001E3Q0012070012001F4Q0004001300054Q00320012000200022Q00650009000900122Q0052000800020001001235000100033Q00066C0004007400013Q00040E3Q007400012Q0004000800043Q000673000700740001000800040E3Q007400012Q0004000800053Q000655000800740001000100040E3Q007400012Q001A000800014Q0068000800053Q001207000800013Q001235000900203Q001207000A00193Q002048000A000A001A2Q002C000B00074Q0032000A00020002001235000B00214Q006500090009000B2Q005200080002000100040E3Q00840001000E2E002200840001000700040E3Q008400012Q0004000800053Q00066C0008008400013Q00040E3Q008400012Q001A00086Q0068000800053Q001207000800013Q001235000900233Q001207000A00193Q002048000A000A001A2Q002C000B00074Q0032000A00020002001235000B00244Q006500090009000B2Q00520008000200012Q0004000800053Q00066C0008009400013Q00040E3Q009400012Q002B000800084Q0068000800063Q001207000800043Q00204800080008002500061800093Q000100052Q00163Q00074Q006B3Q00034Q00163Q00084Q00163Q00094Q00163Q000A4Q00520008000200012Q007D00025Q00040E3Q00050001001207000800263Q0020480008000800270020480008000800280020480008000800290006550008009F0001000100040E3Q009F00010012070009000C3Q001235000A002A4Q00520009000200012Q007D00025Q00040E3Q000500012Q0004000900063Q00066C000900192Q013Q00040E3Q00192Q01002048000A0009002B00066C000A00192Q013Q00040E3Q00192Q01002048000A0009002C0006453Q00C30001000A00040E3Q00C300012Q0004000A000B4Q0064000A000A000900066C000A00B100013Q00040E3Q00B10001002602000A00B10001002D00040E3Q00B10001002048000B000A002E000655000B00B20001000100040E3Q00B20001001235000B002F3Q00066C000A00B900013Q00040E3Q00B90001002602000A00B90001002D00040E3Q00B90001002048000C000A0030000655000C00BA0001000100040E3Q00BA0001001235000C002F3Q001207000D00013Q001235000E00314Q002C000F000B3Q0012350010001C4Q002C0011000C3Q001235001200324Q0065000E000E00122Q0052000D000200010020483Q0009002C00204E000A0009000A001235000C000B4Q006F000A000C0002000655000A00D00001000100040E3Q00D0000100204E000A0009000A001235000C00334Q006F000A000C0002000655000A00D00001000100040E3Q00D0000100204E000A0009000A001235000C00344Q006F000A000C000200066C000A001F2Q013Q00040E3Q001F2Q01002048000B000A0035002048000C000B0036002048000D00030035002048000D000D00362Q0075000C000C000D002048000D000B0037002048000E00030035002048000E000E00372Q0075000D000D000E002048000E000B0038002048000F00030035002048000F000F00382Q0075000E000E000F001207000F00193Q002048000F000F00392Q00080010000C000C2Q00080011000D000D2Q00530010001000112Q00080011000E000E2Q00530010001000112Q0032000F000200022Q0004001000044Q00040011000C4Q0053001000100011000620000700020001001000040E3Q00ED00012Q001700106Q001A001000014Q00040011000D3Q00061C001100062Q01000F00040E3Q00062Q01000655001000062Q01000100040E3Q00062Q01001207001100013Q0012350012003A3Q00204800130009002C0012350014003B3Q001207001500193Q00204800150015001A2Q002C0016000F4Q00320015000200022Q00650012001200152Q0052001100020001001207001100043Q00204800110011002500061800120001000100042Q00163Q00074Q006B3Q00034Q006B3Q00094Q00163Q000D4Q005200110002000100040E3Q001F2Q010006550010001F2Q01000100040E3Q001F2Q01001207001100193Q0020480011001100392Q00080012000C000C2Q00080013000E000E2Q00530012001200132Q0032001100020002000E63003C001F2Q01001100040E3Q001F2Q01001207001100013Q0012350012003D3Q00204800130009002C2Q00650012001200132Q00520011000200010012070011003E3Q0012070012003F4Q005200110002000100040E3Q001F2Q010026023Q001F2Q01004000040E3Q001F2Q01001207000A00013Q001235000B00414Q0052000A000200012Q002B8Q007D00025Q00040E3Q000500012Q007D00025Q00040E3Q0005000100040E3Q000500012Q00143Q00013Q00023Q00023Q00026Q004E4003083Q00536166655A6F6E65000C4Q00048Q0004000100013Q00061800023Q000100012Q00163Q00024Q002B000300033Q001235000400014Q0004000500034Q0004000600044Q0001000500050006001235000600024Q003D3Q000600012Q00143Q00013Q00018Q00034Q00048Q00103Q00024Q00143Q00017Q00013Q0003043Q004E616D65000D4Q00048Q0004000100013Q00061800023Q000100012Q00163Q00023Q00061800030001000100032Q00163Q00024Q00163Q00034Q00163Q00014Q002B000400054Q0004000600023Q0020480006000600012Q003D3Q000600012Q00143Q00013Q00023Q000C3Q0003063Q00506172656E74030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403083Q00522Q6F745061727403043Q004865616403073Q00566563746F72332Q033Q006E657703083Q00506F736974696F6E03013Q0058026Q00244003013Q005903013Q005A00274Q00047Q00066C3Q002400013Q00040E3Q002400012Q00047Q0020485Q000100066C3Q002400013Q00040E3Q002400012Q00047Q00204E5Q0002001235000200034Q006F3Q000200020006553Q00170001000100040E3Q001700012Q00047Q00204E5Q0002001235000200044Q006F3Q000200020006553Q00170001000100040E3Q001700012Q00047Q00204E5Q0002001235000200054Q006F3Q0002000200066C3Q002400013Q00040E3Q00240001001207000100063Q00204800010001000700204800023Q000800204800020002000900203400020002000A00204800033Q000800204800030003000B00204800043Q000800204800040004000C2Q002F000100044Q007200016Q002B8Q00103Q00024Q00143Q00017Q00093Q00030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403083Q00522Q6F745061727403043Q004865616403043Q006D6174682Q033Q0061627303083Q00506F736974696F6E03013Q0059026Q002040012D4Q000400015Q00066C0001001300013Q00040E3Q001300012Q000400015Q00204E000100010001001235000300024Q006F000100030002000655000100130001000100040E3Q001300012Q000400015Q00204E000100010001001235000300034Q006F000100030002000655000100130001000100040E3Q001300012Q000400015Q00204E000100010001001235000300044Q006F00010003000200066C0001002600013Q00040E3Q002600012Q0004000200013Q0006733Q00230001000200040E3Q00230001001207000200053Q0020480002000200062Q0004000300023Q0020480003000300070020480003000300080020480004000100070020480004000400082Q00750003000300042Q003200020002000200261D000200240001000900040E3Q002400012Q001700026Q001A000200014Q0010000200024Q0004000200013Q0006203Q00020001000200040E3Q002A00012Q001700026Q001A000200014Q0010000200024Q00143Q00017Q00", GetFEnv(), ...);