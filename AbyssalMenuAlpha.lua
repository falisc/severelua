-- @PTACUNIT
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
											local A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
										else
											Stk[Inst[2]] = Inst[3] ~= 0;
											VIP = VIP + 1;
										end
									elseif (Enum > 2) then
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
										do
											return Stk[A](Unpack(Stk, A + 1, Inst[3]));
										end
									end
								elseif (Enum <= 5) then
									if (Enum > 4) then
										local A = Inst[2];
										Stk[A](Stk[A + 1]);
									else
										do
											return;
										end
									end
								elseif (Enum > 6) then
									if (Stk[Inst[2]] ~= Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = {};
								end
							elseif (Enum <= 11) then
								if (Enum <= 9) then
									if (Enum > 8) then
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A = Inst[2];
										local T = Stk[A];
										local B = Inst[3];
										for Idx = 1, B do
											T[Idx] = Stk[A + Idx];
										end
									end
								elseif (Enum > 10) then
									local B = Stk[Inst[4]];
									if B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								else
									local A = Inst[2];
									local T = Stk[A];
									local B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								end
							elseif (Enum <= 13) then
								if (Enum == 12) then
									Stk[Inst[2]] = Inst[3] ~= 0;
								else
									local A = Inst[2];
									Stk[A] = Stk[A]();
								end
							elseif (Enum == 14) then
								Stk[Inst[2]] = Inst[3];
							else
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							end
						elseif (Enum <= 23) then
							if (Enum <= 19) then
								if (Enum <= 17) then
									if (Enum == 16) then
										local A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
									else
										Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
									end
								elseif (Enum == 18) then
									local A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
								else
									Stk[Inst[2]] = #Stk[Inst[3]];
								end
							elseif (Enum <= 21) then
								if (Enum > 20) then
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
							elseif (Enum > 22) then
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							else
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
							end
						elseif (Enum <= 27) then
							if (Enum <= 25) then
								if (Enum > 24) then
									Stk[Inst[2]] = Inst[3];
								else
									Stk[Inst[2]] = {};
								end
							elseif (Enum == 26) then
								Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
							end
						elseif (Enum <= 29) then
							if (Enum > 28) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							else
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							end
						elseif (Enum > 30) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
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
					elseif (Enum <= 47) then
						if (Enum <= 39) then
							if (Enum <= 35) then
								if (Enum <= 33) then
									if (Enum == 32) then
										if (Stk[Inst[2]] == Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Stk[Inst[2]] > Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = VIP + Inst[3];
									end
								elseif (Enum > 34) then
									Stk[Inst[2]] = Env[Inst[3]];
								else
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
								end
							elseif (Enum <= 37) then
								if (Enum > 36) then
									VIP = Inst[3];
								elseif (Inst[2] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 38) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
									if (Stk[Inst[2]] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = not Stk[Inst[3]];
								end
							elseif (Enum == 42) then
								if (Stk[Inst[2]] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum <= 45) then
							if (Enum == 44) then
								Stk[Inst[2]] = not Stk[Inst[3]];
							else
								local A = Inst[2];
								do
									return Unpack(Stk, A, A + Inst[3]);
								end
							end
						elseif (Enum > 46) then
							local A = Inst[2];
							local T = Stk[A];
							for Idx = A + 1, Inst[3] do
								Insert(T, Stk[Idx]);
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
						end
					elseif (Enum <= 55) then
						if (Enum <= 51) then
							if (Enum <= 49) then
								if (Enum == 48) then
									if (Inst[2] < Stk[Inst[4]]) then
										VIP = Inst[3];
									else
										VIP = VIP + 1;
									end
								else
									Stk[Inst[2]]();
								end
							elseif (Enum > 50) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							end
						elseif (Enum <= 53) then
							if (Enum == 52) then
								if (Inst[2] < Stk[Inst[4]]) then
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
						elseif (Enum > 54) then
							Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
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
					elseif (Enum <= 59) then
						if (Enum <= 57) then
							if (Enum > 56) then
								do
									return Stk[Inst[2]];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
							end
						elseif (Enum > 58) then
							local A = Inst[2];
							Stk[A](Stk[A + 1]);
						else
							Stk[Inst[2]] = Env[Inst[3]];
						end
					elseif (Enum <= 61) then
						if (Enum > 60) then
							local B = Stk[Inst[4]];
							if B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						end
					elseif (Enum <= 62) then
						Stk[Inst[2]][Inst[3]] = Inst[4];
					elseif (Enum == 63) then
						if (Stk[Inst[2]] > Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = VIP + Inst[3];
						end
					else
						Stk[Inst[2]] = Inst[3] / Stk[Inst[4]];
					end
				elseif (Enum <= 96) then
					if (Enum <= 80) then
						if (Enum <= 72) then
							if (Enum <= 68) then
								if (Enum <= 66) then
									if (Enum == 65) then
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									else
										Stk[Inst[2]] = Upvalues[Inst[3]];
									end
								elseif (Enum == 67) then
									if (Stk[Inst[2]] > Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]][Inst[3]] = Inst[4];
								end
							elseif (Enum <= 70) then
								if (Enum == 69) then
									local A = Inst[2];
									Stk[A] = Stk[A]();
								elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 71) then
								VIP = Inst[3];
							else
								do
									return;
								end
							end
						elseif (Enum <= 76) then
							if (Enum <= 74) then
								if (Enum > 73) then
									Stk[Inst[2]] = Stk[Inst[3]];
								else
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								end
							elseif (Enum > 75) then
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
									if (Mvm[1] == 43) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
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
						elseif (Enum <= 78) then
							if (Enum == 77) then
								Stk[Inst[2]]();
							elseif (Stk[Inst[2]] < Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 79) then
							do
								return Stk[Inst[2]];
							end
						else
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 88) then
						if (Enum <= 84) then
							if (Enum <= 82) then
								if (Enum == 81) then
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Stk[Inst[2]] < Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 83) then
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
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							end
						elseif (Enum <= 86) then
							if (Enum > 85) then
								Stk[Inst[2]] = #Stk[Inst[3]];
							else
								local A = Inst[2];
								local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum > 87) then
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
						elseif (Stk[Inst[2]] == Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 92) then
						if (Enum <= 90) then
							if (Enum == 89) then
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
							elseif (Inst[2] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 91) then
							Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
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
					elseif (Enum <= 94) then
						if (Enum == 93) then
							Stk[Inst[2]] = Inst[3] ~= 0;
						else
							local B = Inst[3];
							local K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
						end
					elseif (Enum == 95) then
						Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
					else
						Stk[Inst[2]] = Inst[3] / Stk[Inst[4]];
					end
				elseif (Enum <= 112) then
					if (Enum <= 104) then
						if (Enum <= 100) then
							if (Enum <= 98) then
								if (Enum > 97) then
									local A = Inst[2];
									local B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								else
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								end
							elseif (Enum == 99) then
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							else
								local B = Stk[Inst[4]];
								if not B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 102) then
							if (Enum > 101) then
								Upvalues[Inst[3]] = Stk[Inst[2]];
							elseif (Inst[2] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 103) then
							local A = Inst[2];
							local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
						end
					elseif (Enum <= 108) then
						if (Enum <= 106) then
							if (Enum == 105) then
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							else
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							end
						elseif (Enum == 107) then
							Upvalues[Inst[3]] = Stk[Inst[2]];
						else
							local B = Stk[Inst[4]];
							if not B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 110) then
						if (Enum == 109) then
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						else
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
						end
					elseif (Enum > 111) then
						local A = Inst[2];
						do
							return Unpack(Stk, A, Top);
						end
					else
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					end
				elseif (Enum <= 120) then
					if (Enum <= 116) then
						if (Enum <= 114) then
							if (Enum == 113) then
								if (Stk[Inst[2]] > Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum == 115) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						else
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
						end
					elseif (Enum <= 118) then
						if (Enum > 117) then
							local B = Inst[3];
							local K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
						elseif (Stk[Inst[2]] <= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum > 119) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					else
						Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
					end
				elseif (Enum <= 124) then
					if (Enum <= 122) then
						if (Enum == 121) then
							if (Inst[2] < Stk[Inst[4]]) then
								VIP = Inst[3];
							else
								VIP = VIP + 1;
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
						end
					elseif (Enum > 123) then
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
							if (Mvm[1] == 43) then
								Indexes[Idx - 1] = {Stk,Mvm[3]};
							else
								Indexes[Idx - 1] = {Upvalues,Mvm[3]};
							end
							Lupvals[#Lupvals + 1] = Indexes;
						end
						Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
					else
						local A = Inst[2];
						local Results = {Stk[A](Stk[A + 1])};
						local Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					end
				elseif (Enum <= 126) then
					if (Enum > 125) then
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
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
				elseif (Enum <= 127) then
					if not Stk[Inst[2]] then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum == 128) then
					Stk[Inst[2]] = Inst[3] ~= 0;
					VIP = VIP + 1;
				elseif (Stk[Inst[2]] ~= Inst[4]) then
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
return VMCall("LOL!EB3Q0003043Q0067616D65030A3Q004765745365727669636503073Q00506C6179657273030B3Q004C6F63616C506C6179657203103Q0055736572496E70757453657276696365030E3Q00466F72676F2Q74656E20442Q657003073Q00566563746F72332Q033Q006E6577021F85EB51B8FE57C002F853E3A51B10B3402Q022B8716D90E27C0030D3Q00416E6369656E742053616E6473024Q33B3E09BC002B81E85EB912DB14002FCA9F1D24DA22F40030C3Q0053756E6B656E2057696C647302894160E55002AD4002FCA9F1D2CDB0AC4002986E1283400B94C0030C3Q0053706972697420522Q6F74730248E17A14AEFE994002378941602583AF4002F6285C8FC2E59DC0028Q00026Q005440026Q002440026Q000840027Q0040026Q003940026Q003E40030A3Q006C6F6164737472696E6703073Q00482Q747047657403443Q00682Q7470733A2Q2F7261772E67697468756275736572636F6E74656E742E636F6D2F7A2Q652D373635342F55492F726566732F68656164732F6D61696E2F55492E6C756103063Q006E6F74696679030C3Q004162792Q73616C204D656E7503093Q005549204C6F6164656403023Q00554903063Q0057696E646F7703053Q005469746C6503243Q004162792Q73616C204D656E75207C204275696C643A20416C706861207C204D617463686103043Q0053697A6503073Q00566563746F7232025Q00407F40025Q00E0754003043Q004F70656E2Q0103053Q005468656D6503063Q00476C6F62616C030B3Q004C69676874412Q63656E7403063Q00436F6C6F723303073Q0066726F6D524742025Q00806640026Q005940025Q00E06F4003063Q00412Q63656E74025Q00406040025Q00805140026Q006940030A3Q004461726B412Q63656E74026Q00444003093Q004C6967687442617365025Q0080414003043Q0042617365026Q003640026Q00324003083Q004461726B42617365026Q002E40026Q00284003043Q0054657874025Q00A06E40025Q00606D4003083Q00436F2Q6C61707365025Q00806B4003063Q00436F726E6572026Q00144003073Q0050612Q64696E67026Q0018402Q033Q0054616203043Q00486F6D6503073Q0053656374696F6E03043Q00496E666F03053Q004C6162656C03253Q0048652Q6C6F2C207468616E6B20796F7520666F72207573696E67206D79207363726970742E03173Q004D616465206279204070746163756E6974202F2066616C03303Q00646D204070746163756E697420666F7220616E7920692Q73756573202F2062756773202F2073752Q67657374696F6E7303083Q00496E7465726E616C03093Q00436F2Q6C617073656403113Q00506572666F726D616E636520537461747303063Q004D656D6F7279030A3Q004D656D6F72793A202Q2D2Q033Q0043505503073Q004350553A202Q2D2Q033Q0047505503073Q004750553A202Q2D03043Q007461736B03053Q00737061776E03073Q004661726D696E6703093Q004175746F204661726D03083Q00436865636B626F7803063Q00456E61626C6503073Q0044656661756C74010003073Q004B657962696E64030F3Q00546F2Q676C65204175746F6661726D2Q033Q004B657903043Q00456E756D03073Q004B6579436F646503013Q005003053Q00706169727303053Q007461626C6503063Q00696E7365727403083Q0044726F70646F776E03093Q004661726D204172656103073Q004F7074696F6E7303063Q00536C6964657203103Q004F787967656E205468726573686F6C642Q033Q004D696E2Q033Q004D617803043Q005374657003063Q0053752Q66697803013Q002503153Q004F787967656E205761726E696E672042752Q666572026Q003440026Q00F03F031D3Q004175746F2053652Q6C202872657175697265732067616D6570612Q732903053Q00437570696403063Q004C6F6E656C7903053Q005368696E7903043Q00502Q6F7003043Q00526F636B03053Q00436F72616C03043Q004D6F2Q7303053Q004D6574616C03043Q0053616E6403063Q00416C62696E6F030B3Q005472616E73706172656E7403063Q0043616374757303063Q0053706972697403063Q00466F2Q73696C03063Q00476F6C64656E03083Q004E6567617469766503053Q00466169727903093Q00496E76697369626C6503043Q004E656F6E030B3Q00556C74726176696F6C657403063Q00522Q6F74656403063Q00536861646F7703073Q00416E67656C696303073Q004162792Q73616C03083Q0047726F756E64656403063Q0042616E616E6103043Q004A61646503063Q004C6971756964030B3Q00466973682046696C74657203283Q0053656C656374206D75746174696F6E7320746F207461726765742028656D707479203D20612Q6C29030D3Q004D756C746944726F70646F776E03093Q004D75746174696F6E7303293Q0053656C656374206669736820747970657320746F207461726765742028656D707479203D20612Q6C29030C3Q00466973682054797065732031030D3Q00416E6369656E7420536861726B030A3Q00416E676C65726669736803093Q0042612Q726163756461030C3Q004269676D6F75746866697368030D3Q00426C61636B66696E2054756E6103083Q00426C6F626669736803093Q00426C75652054616E67030C3Q00426C756566696E2054756E6103083Q00436176656669736803093Q00436C6F776E666973682Q033Q00436F6403063Q00446973637573030A3Q00447261676F6E6669736803073Q004579656669736803073Q0047726F75706572030C3Q0048612Q6D657220536861726B03133Q00496E666C617465642050752Q66657266697368030C3Q004A616775617220536861726B03093Q004A652Q6C7966697368030F3Q004B696E6720416E676C65726669736803083Q004C696F6E6669736803093Q004D616869204D616869030C3Q00466973682054797065732032030A3Q004D6F736173617572757303083Q004E61706F6C656F6E03073Q004E61727768616C030F3Q00506163696669632046616E66697368030B3Q0050656C6963616E2045656C03073Q00506972616E686103073Q00506F6D70616E6F030A3Q0050752Q66657266697368030D3Q005361636162616D62617370697303083Q005361696C6669736803063Q0053616C6D6F6E030C3Q0053636F7270696F6E6669736803093Q0053656120486F727365030A3Q0053656120547572746C6503053Q00536861726B03053Q00537175696403073Q0053756E6669736803083Q0054616D626171756903043Q0054616E67030B3Q00546F7563616E204669736803053Q0054726F757403053Q005768616C65030D3Q0052657365742046696C7465727303063Q0042752Q746F6E032C3Q004661726D2053652Q74696E6773205B44616E6765726F75732C204564697420776974682043617574696F6E5D032D3Q0074772Q656E4475726174696F6E202D205365636F6E647320746F20436F6D706C65746520416E696D6174696F6E030E3Q0054772Q656E204475726174696F6E026Q00E03F03013Q007303153Q00526573657420746F2044656661756C74202833732903313Q007265747265617453702Q65644D756C7469706C696572202D204D756C7469706C69657320526574726561742053702Q656403133Q00526574726561742053702Q6564204D756C746903013Q007803153Q00526573657420746F2044656661756C74202832782903203Q006D696E44697374202D20466973682053682Q6F74696E672044697374616E6365030C3Q004D696E2044697374616E636503063Q00207374756473031B3Q00526573657420746F2044656661756C74202832352073747564732903233Q0074772Q656E5374657073202D20506F736974696F6E2055706461746520416D6F756E74030B3Q0054772Q656E20537465707303153Q00526573657420746F2044656661756C74202833302903083Q0054656C65706F727403093Q004C6F636174696F6E7303043Q004D69736303093Q005574696C697469657303213Q00546869732069732061206E6F636C697020616E7469636865617420627970612Q7303223Q00596F752077692Q6C206861766520746F2072656A6F696E20746F2064697361626C6503283Q005468657265666F726520796F752063612Q6E6F7420746F756368206C616E64206E6F722073652Q6C030E3Q00456E61626C65204E6F2D636C697003083Q0053652Q74696E6773030D3Q004D61696E2053652Q74696E6773030A3Q00546F2Q676C652047554903013Q004C00B5022Q00123A3Q00013Q0020625Q0002001219000200034Q00333Q0002000200201500013Q000400123A000200013Q002062000200020002001219000400054Q00330002000400022Q000600033Q000400123A000400073Q002015000400040008001219000500093Q0012190006000A3Q0012190007000B4Q003300040007000200103C00030006000400123A000400073Q0020150004000400080012190005000D3Q0012190006000E3Q0012190007000F4Q003300040007000200103C0003000C000400123A000400073Q002015000400040008001219000500113Q001219000600123Q001219000700134Q003300040007000200103C00030010000400123A000400073Q002015000400040008001219000500153Q001219000600163Q001219000700174Q003300040007000200103C000300140004001219000400064Q00320005000300042Q005D00065Q001219000700183Q001219000800193Q0012190009001A4Q005D000A6Q005D000B6Q005D000C6Q0016000D000D4Q0006000E5Q001219000F001B3Q0012190010001C3Q0012190011001D3Q0012190012001E4Q00770013000F00122Q005D00146Q000600156Q000600166Q000600176Q000600186Q000600196Q0006001A6Q0006001B5Q00064C001C3Q000100042Q002B3Q001A4Q002B3Q001B4Q002B3Q00154Q002B3Q00163Q00064C001D0001000100052Q002B3Q00154Q002B3Q00164Q002B3Q00194Q002B3Q001A4Q002B3Q001B3Q000211001E00023Q00064C001F0003000100012Q002B3Q00013Q00064C00200004000100092Q002B3Q000B4Q002B3Q00014Q002B3Q00124Q002B3Q00134Q002B3Q001E4Q002B3Q00064Q002B3Q000C4Q002B3Q000E4Q002B3Q001F3Q00064C00210005000100032Q002B3Q00014Q002B3Q001E4Q002B3Q001F3Q00064C00220006000100042Q002B3Q000D4Q002B3Q00014Q002B3Q000C4Q002B3Q00063Q00123A0023001F3Q00123A002400013Q002062002400240020001219002600214Q0078002400264Q001F00233Q00022Q003100230001000100123A002300223Q001219002400233Q001219002500243Q0012190026001A4Q004F00230026000100123A002300253Q0020620023002300262Q000600253Q000300304400250027002800123A0026002A3Q0020150026002600080012190027002B3Q0012190028002C4Q003300260028000200103C0025002900260030440025002D002E2Q003300230025000200201500240023002F00201500240024003000123A002500323Q002015002500250033001219002600343Q001219002700353Q001219002800364Q003300250028000200103C00240031002500201500240023002F00201500240024003000123A002500323Q002015002500250033001219002600383Q001219002700393Q0012190028003A4Q003300250028000200103C00240037002500201500240023002F00201500240024003000123A002500323Q002015002500250033001219002600193Q0012190027003C3Q001219002800384Q003300250028000200103C0024003B002500201500240023002F00201500240024003000123A002500323Q0020150025002500330012190026003E3Q0012190027001E3Q0012190028003C4Q003300250028000200103C0024003D002500201500240023002F00201500240024003000123A002500323Q002015002500250033001219002600403Q001219002700413Q0012190028001D4Q003300250028000200103C0024003F002500201500240023002F00201500240024003000123A002500323Q002015002500250033001219002600433Q001219002700443Q001219002800414Q003300250028000200103C00240042002500201500240023002F00201500240024003000123A002500323Q002015002500250033001219002600463Q001219002700473Q001219002800364Q003300250028000200103C00240045002500201500240023002F00201500240024003000123A002500323Q0020150025002500330012190026003A3Q001219002700343Q001219002800494Q003300250028000200103C00240048002500201500240023002F0020150024002400300030440024004A004B00201500240023002F0020150024002400300030440024004C004D00206200240023004E2Q000600263Q000100304400260027004F2Q00330024002600020020620025002400502Q000600273Q00010030440027002700512Q00330025002700020020620026002500522Q000600283Q00010030440028002700532Q004F0026002800010020620026002500522Q000600283Q00010030440028002700542Q004F0026002800010020620026002500522Q000600283Q00010030440028002700552Q004F00260028000100201500260025005600304400260057002E0020620026002400502Q000600283Q00010030440028002700582Q003300260028000200201500270026005600304400270057002E2Q000600273Q00030020620028002600522Q0006002A3Q0001003044002A0027005A2Q00330028002A000200103C0027005900280020620028002600522Q0006002A3Q0001003044002A0027005C2Q00330028002A000200103C0027005B00280020620028002600522Q0006002A3Q0001003044002A0027005E2Q00330028002A000200103C0027005D002800123A0028005F3Q00201500280028006000064C00290007000100022Q002B3Q00234Q002B3Q00274Q003B00280002000100206200280023004E2Q0006002A3Q0001003044002A002700612Q00330028002A00020020620029002800502Q0006002B3Q0001003044002B002700622Q00330029002B0002002062002A002900632Q0006002C3Q0002003044002C00270064003044002C0065006600064C002D0008000100062Q002B3Q00064Q002B3Q00014Q002B3Q001F4Q002B3Q001E4Q002B3Q000B4Q002B3Q000D4Q004F002A002D0001002062002A002900672Q0006002C3Q0002003044002C0027006800123A002D006A3Q002015002D002D006B002015002D002D006C00103C002C0069002D00064C002D0009000100062Q002B3Q00064Q002B3Q00014Q002B3Q001F4Q002B3Q001E4Q002B3Q000B4Q002B3Q000D3Q000211002E000A4Q004F002A002E00012Q0006002A5Q00123A002B006D4Q004A002C00034Q007B002B0002002D0004253Q00252Q0100123A0030006E3Q00201500300030006F2Q004A0031002A4Q004A0032002E4Q004F003000320001000653002B00202Q0100020004253Q00202Q01002062002B002900702Q0006002D3Q0003003044002D0027007100103C002D0072002A00103C002D0065000400064C002E000B000100032Q002B3Q00044Q002B3Q00054Q002B3Q00034Q004F002B002E0001002062002B002900732Q0006002D3Q0006003044002D00270074003044002D0075001A003044002D00760035003044002D0077004B00103C002D00650008003044002D0078007900064C002E000C000100012Q002B3Q00084Q004F002B002E0001002062002B002900732Q0006002D3Q0006003044002D0027007A003044002D00750018003044002D0076007B003044002D0077007C003044002D0065001A003044002D0078007900064C002E000D000100012Q002B3Q00094Q004F002B002E0001002062002B002900632Q0006002D3Q0002003044002D0027007D003044002D0065006600064C002E000E000100012Q002B3Q00144Q004F002B002E00012Q0006002B00163Q001219002C007E3Q001219002D007F3Q001219002E00803Q001219002F00813Q001219003000823Q001219003100833Q001219003200843Q001219003300853Q001219003400863Q001219003500873Q001219003600883Q001219003700893Q0012190038008A3Q0012190039008B3Q001219003A008C3Q001219003B008D3Q001219003C008E3Q001219003D008F3Q001219003E00903Q001219003F00913Q001219004000923Q001219004100933Q001219004200943Q001219004300953Q001219004400963Q001219004500973Q001219004600983Q001219004700994Q0008002B001C00012Q0016002C002E3Q002062002F002800502Q000600313Q000100304400310027009A2Q0033002F003100020020620030002F00522Q000600323Q000100304400320027009B2Q004F0030003200010020620030002F009C2Q000600323Q000300304400320027009D00103C00320072002B2Q000600335Q00103C00320065003300064C0033000F000100032Q002B3Q00154Q002B3Q001C4Q002B3Q00194Q00330030003300022Q004A002C00303Q0020620030002F00522Q000600323Q000100304400320027009E2Q004F0030003200010020620030002F009C2Q000600323Q000300304400320027009F2Q0006003300133Q001219003400A03Q001219003500A13Q001219003600A23Q001219003700A33Q001219003800A43Q001219003900A53Q001219003A00A63Q001219003B00A73Q001219003C00A83Q001219003D00A93Q001219003E00AA3Q001219003F00AB3Q001219004000AC3Q001219004100AD3Q001219004200AE3Q001219004300AF3Q001219004400B03Q001219004500B13Q001219004600B23Q001219004700B33Q001219004800B43Q001219004900B54Q000800330016000100103C0032007200332Q000600335Q00103C00320065003300064C00330010000100052Q002B3Q00174Q002B3Q00184Q002B3Q00164Q002B3Q001C4Q002B3Q00194Q00330030003300022Q004A002D00303Q0020620030002F009C2Q000600323Q00030030440032002700B62Q0006003300133Q001219003400B73Q001219003500B83Q001219003600B93Q001219003700BA3Q001219003800BB3Q001219003900BC3Q001219003A00BD3Q001219003B00BE3Q001219003C00BF3Q001219003D00C03Q001219003E00C13Q001219003F00C23Q001219004000C33Q001219004100C43Q001219004200C53Q001219004300C63Q001219004400C73Q001219004500C83Q001219004600C93Q001219004700CA3Q001219004800CB3Q001219004900CC4Q000800330016000100103C0032007200332Q000600335Q00103C00320065003300064C00330011000100052Q002B3Q00184Q002B3Q00174Q002B3Q00164Q002B3Q001C4Q002B3Q00194Q00330030003300022Q004A002E00303Q0020620030002F00522Q000600323Q00010030440032002700CD2Q004F0030003200010020620030002F00CE2Q000600323Q00010030440032002700CD00064C00330012000100092Q002B3Q00154Q002B3Q00174Q002B3Q00184Q002B3Q00164Q002B3Q002C4Q002B3Q002D4Q002B3Q002E4Q002B3Q001C4Q002B3Q00194Q004F0030003300010020620030002800502Q000600323Q00010030440032002700CF2Q00330030003200020020620031003000522Q000600333Q00010030440033002700D02Q004F0031003300010020620031003000732Q000600333Q00060030440033002700D100304400330075007C00304400330076001A0030440033007700D200304400330065001B0030440033007800D300064C00340013000100032Q002B3Q000F4Q002B3Q00134Q002B3Q00124Q00330031003400020020620032003000CE2Q000600343Q00010030440034002700D400064C00350014000100012Q002B3Q00314Q004F0032003500010020620032003000522Q000600343Q00010030440034002700D52Q004F0032003400010020620032003000732Q000600343Q00060030440034002700D600304400340075007C00304400340076004B0030440034007700D200304400340065001C0030440034007800D700064C00350015000100012Q002B3Q00104Q00330032003500020020620033003000CE2Q000600353Q00010030440035002700D800064C00360016000100012Q002B3Q00324Q004F0033003600010020620033003000522Q000600353Q00010030440035002700D92Q004F0033003500010020620033003000732Q000600353Q00060030440035002700DA00304400350075004B00304400350076003500304400350077004B00304400350065003C0030440035007800DB00064C00360017000100012Q002B3Q00114Q00330033003600020020620034003000CE2Q000600363Q00010030440036002700DC00064C00370018000100012Q002B3Q00334Q004F0034003700010020620034003000522Q000600363Q00010030440036002700DD2Q004F0034003600010020620034003000732Q000600363Q00050030440036002700DE00304400360075001A00304400360076003500304400360077004B00304400360065001E00064C00370019000100032Q002B3Q00124Q002B3Q00134Q002B3Q000F4Q00330034003700020020620035003000CE2Q000600373Q00010030440037002700DF00064C0038001A000100012Q002B3Q00344Q004F00350038000100206200350023004E2Q000600373Q00010030440037002700E02Q00330035003700020020620036003500502Q000600383Q00010030440038002700E12Q003300360038000200123A0037006D4Q004A003800034Q007B0037000200390004253Q00530201002062003C003600CE2Q0006003E3Q000100103C003E0027003A00064C003F001B000100032Q002B3Q00214Q002B3Q003B4Q002B3Q003A4Q004F003C003F00012Q0058003A5Q0006530037004A020100020004253Q004A020100206200370023004E2Q000600393Q00010030440039002700E22Q00330037003900020020620038003700502Q0006003A3Q0001003044003A002700E32Q00330038003A00020020620039003800522Q0006003B3Q0001003044003B002700E42Q004F0039003B00010020620039003800522Q0006003B3Q0001003044003B002700E52Q004F0039003B00010020620039003800522Q0006003B3Q0001003044003B002700E62Q004F0039003B00010020620039003800CE2Q0006003B3Q0001003044003B002700E700064C003C001C000100012Q002B3Q00014Q004F0039003C000100206200390023004E2Q0006003B3Q0001003044003B002700E82Q00330039003B0002002062003A003900502Q0006003C3Q0001003044003C002700E92Q0033003A003C0002002062003B003A00672Q0006003D3Q0002003044003D002700EA00123A003E006A3Q002015003E003E006B002015003E003E00EB00103C003D0069003E00064C003E001D000100012Q002B3Q00233Q000211003F001E4Q004F003B003F000100123A003B005F3Q002015003B003B006000064C003C001F0001000A2Q002B3Q00064Q002B3Q000A4Q002B3Q000C4Q002B3Q00014Q002B3Q000E4Q002B3Q001D4Q002B3Q00074Q002B3Q00084Q002B3Q00094Q002B3Q000D4Q003B003B0002000100123A003B005F3Q002015003B003B006000064C003C0020000100052Q002B3Q000C4Q002B3Q00064Q002B3Q000D4Q002B3Q000A4Q002B3Q00014Q003B003B0002000100123A003B005F3Q002015003B003B006000064C003C0021000100032Q002B3Q00064Q002B3Q000C4Q002B3Q00014Q003B003B0002000100123A003B005F3Q002015003B003B006000064C003C0022000100102Q002B3Q00064Q002B3Q000B4Q002B3Q000C4Q002B3Q00014Q002B3Q00074Q002B3Q00084Q002B3Q000A4Q002B3Q00144Q002B3Q00224Q002B3Q000D4Q002B3Q00204Q002B3Q00054Q002B3Q00134Q002B3Q00104Q002B3Q00094Q002B3Q00114Q003B003B000200012Q00043Q00013Q00233Q00023Q0003063Q006970616972732Q0100154Q00068Q006B8Q00068Q006B3Q00013Q00123A3Q00014Q0042000100024Q007B3Q000200020004253Q000A00012Q004200055Q00201A0005000400020006533Q0008000100020004253Q0008000100123A3Q00014Q0042000100034Q007B3Q000200020004253Q001200012Q0042000500013Q00201A0005000400020006533Q0010000100020004253Q001000012Q00043Q00017Q000D3Q00028Q00030E3Q0046696E6446697273744368696C6403043Q004865616403083Q00522Q6F7450617274010003053Q00737461747303043Q004669736803083Q004D75746174696F6E03053Q004C6162656C03083Q00666973685479706503043Q0054657874030C3Q00666973684D75746174696F6E3Q01634Q004200016Q0056000100013Q000E7900010005000100010004253Q000500012Q008000016Q005D000100014Q0042000200014Q0056000200023Q000E790001000B000100020004253Q000B00012Q008000026Q005D000200013Q00067F00010012000100010004253Q0012000100067F00020012000100010004253Q001200012Q005D000300014Q0050000300024Q0042000300024Q0032000300033Q00067F00030048000100010004253Q0048000100206200043Q0002001219000600034Q003300040006000200067F0004001E000100010004253Q001E000100206200043Q0002001219000600044Q003300040006000200067F00040024000100010004253Q002400012Q0042000500023Q00201A00053Q00052Q005D00056Q0050000500023Q002062000500040002001219000700064Q003300050007000200067F0005002D000100010004253Q002D00012Q0042000600023Q00201A00063Q00052Q005D00066Q0050000600023Q002062000600050002001219000800074Q0033000600080002002062000700050002001219000900084Q003300070009000200060B00080038000100070004253Q00380001002062000800070002001219000A00094Q00330008000A00020006510006003C00013Q0004253Q003C000100067F00080040000100010004253Q004000012Q0042000900023Q00201A00093Q00052Q005D00096Q0050000900024Q000600093Q0002002015000A0006000B00103C0009000A000A002015000A0008000B00103C0009000C000A2Q004A000300094Q0042000900024Q001C00093Q00030026570003004C000100050004253Q004C00012Q005D00046Q0050000400023Q0006510001005400013Q0004253Q005400012Q0042000400033Q00201500050003000C2Q0032000400040005002681000400540001000D0004253Q005400012Q008000046Q005D000400013Q0006510002005D00013Q0004253Q005D00012Q0042000500043Q00201500060003000A2Q00320005000500060026810005005D0001000D0004253Q005D00012Q008000056Q005D000500013Q00060B00060061000100040004253Q006100012Q004A000600054Q0050000600024Q00043Q00017Q00073Q0003063Q00747970656F6603083Q00496E7374616E636503063Q00697061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103083Q004261736550617274030A3Q0043616E436F2Q6C696465021B3Q0006513Q000700013Q0004253Q0007000100123A000200014Q004A00036Q001000020002000200268100020008000100020004253Q000800012Q00043Q00013Q00123A000200033Q00206200033Q00042Q004B000300044Q005500023Q00040004253Q0018000100123A000700014Q004A000800064Q001000070002000200265700070018000100020004253Q00180001002062000700060005001219000900064Q00330007000900020006510007001800013Q0004253Q0018000100103C0006000700010006530002000D000100020004253Q000D00012Q00043Q00017Q00073Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403163Q00412Q73656D626C794C696E65617256656C6F6369747903073Q00566563746F72332Q033Q006E6577028Q0001143Q00066C0001000400013Q0004253Q000400012Q004200015Q00201500010001000100067F00010007000100010004253Q000700012Q00043Q00013Q002062000200010002001219000400034Q00330002000400020006510002001300013Q0004253Q0013000100123A000300053Q002015000300030006001219000400073Q001219000500073Q001219000600074Q003300030006000200103C0002000400032Q00043Q00017Q00213Q0003063Q00506172656E7403093Q0043686172616374657203083Q00506F736974696F6E028Q00026Q00F03F027Q004003063Q00747970656F6603073Q00566563746F723303093Q004D61676E6974756465026Q00244003063Q006E756D62657203083Q00536166655A6F6E652Q0103043Q007461736B03053Q0064656C6179026Q002E4003013Q005803013Q005903013Q005A03043Q006D61746803043Q00737172742Q033Q006E657703093Q00776F726B737061636503043Q0047616D6503053Q005475626573030E3Q0046696E6446697273744368696C6403043Q004E616D6503083Q00522Q6F7450617274025Q00804640026Q00144003053Q007063612Q6C030B3Q006D6F75736531636C69636B03043Q007761697406BA3Q0006513Q000500013Q0004253Q0005000100201500063Q000100067F00060008000100010004253Q000800012Q005D00066Q006B00066Q00043Q00014Q0042000600013Q00201500060006000200066C0007000D000100030004253Q000D00012Q0042000700023Q00066C00080010000100040004253Q001000012Q0042000800033Q00201500093Q0003001219000A00044Q005D000B00014Q006B000B6Q0042000B00044Q004A000C00064Q005D000D6Q004F000B000D0001001219000B00054Q004A000C00073Q001219000D00053Q000435000B00AE00012Q0042000F00053Q000651000F00AE00013Q0004253Q00AE00012Q0042000F5Q000651000F00AE00013Q0004253Q00AE00012Q0042000F00063Q000651000F002600013Q0004253Q002600010004253Q00AE00012Q004A000F00014Q000D000F0001000200201500103Q0003000651000F00AE00013Q0004253Q00AE000100067F0010002E000100010004253Q002E00010004253Q00AE00012Q000F000A000A0008000E5A000600570001000A0004253Q00570001001219001100043Q00123A001200074Q004A001300104Q00100012000200020026570012003F000100080004253Q003F000100123A001200074Q004A001300094Q00100012000200020026570012003F000100080004253Q003F00012Q00490012001000090020150011001200090004253Q004000010012190011000A3Q00123A001200074Q004A001300114Q0010001200020002002657001200550001000B0004253Q0055000100264E00110055000100050004253Q00550001000651000500AE00013Q0004253Q00AE0001002681000500AE0001000C0004253Q00AE00012Q0042001200073Q00201A00120005000D00123A0012000E3Q00201500120012000F001219001300103Q00064C00143Q000100022Q001B3Q00074Q002B3Q00054Q004F0012001400010004253Q00AE00012Q004A000900103Q001219000A00043Q0020150011000F00110020150012001000112Q00490011001100120020150012000F00120020150013001000122Q00490012001200130020150013000F00130020150014001000132Q004900130013001400123A001400143Q0020150014001400152Q00220015001100112Q00220016001200122Q000F0015001500162Q00220016001300132Q000F0015001500162Q00100014000200020006510002007000013Q0004253Q007000012Q004A001500024Q004A001600144Q00100015000200020006510015007000013Q0004253Q007000010004253Q00AE00012Q004900150007000E00206D00150015000500104000150005001500123A001600083Q0020150016001600160020150017001000110020150018000F00110020150019001000112Q00490018001800192Q00220018001800152Q000F0017001700180020150018001000120020150019000F0012002015001A001000122Q004900190019001A2Q00220019001900152Q000F001800180019002015001900100013002015001A000F0013002015001B001000132Q0049001A001A001B2Q0022001A001A00152Q000F00190019001A2Q00330016001900022Q0042001700084Q004A001800064Q003B00170002000100103C3Q0003001600123A001700173Q00201500170017001800201500170017001900206200170017001A2Q0042001900013Q00201500190019001B2Q00330017001900020006510017009C00013Q0004253Q009C000100206200180017001A001219001A001C4Q00330018001A00020006510018009C00013Q0004253Q009C000100201500180017001C00103C00180003001600123A001800143Q0020150018001800152Q00220019001100112Q0022001A001300132Q000F00190019001A2Q001000180002000200264E001400A90001001D0004253Q00A90001000E65001E00A9000100180004253Q00A9000100123A0019001F3Q00123A001A00204Q003B00190002000100123A0019000E3Q0020150019001900212Q004A001A00084Q003B001900020001000414000B001C00012Q0042000B00084Q0042000C00013Q002015000C000C00022Q003B000B000200012Q0042000B00044Q0042000C00013Q002015000C000C00022Q005D000D00014Q004F000B000D00012Q005D000B6Q006B000B6Q00043Q00013Q00013Q00015Q00044Q00428Q0042000100013Q00201A3Q000100012Q00043Q00017Q00183Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403083Q00506F736974696F6E03013Q005803013Q005903013Q005A03043Q006D61746803043Q0073717274026Q0008402Q033Q006D6178026Q00244003053Q00666C2Q6F7202FCA9F1D24D62903F026Q00F03F03073Q00566563746F72332Q033Q006E657703093Q00776F726B737061636503043Q0047616D6503053Q00547562657303043Q004E616D6503083Q00522Q6F745061727403043Q007461736B03043Q007761697402734Q004200025Q00201500020002000100060B00030007000100020004253Q00070001002062000300020002001219000500034Q003300030005000200067F0003000A000100010004253Q000A00012Q00043Q00014Q0042000400014Q004A000500024Q005D00066Q004F00040006000100201500040003000400201500053Q00050020150006000400052Q004900050005000600201500063Q00060020150007000400062Q004900060006000700201500073Q00070020150008000400072Q004900070007000800123A000800083Q0020150008000800092Q00220009000500052Q0022000A000600062Q000F00090009000A2Q0022000A000700072Q000F00090009000A2Q00100008000200020012190009000A3Q00123A000A00083Q002015000A000A000B001219000B000C3Q00123A000C00083Q002015000C000C000D2Q0077000D000800092Q004B000C000D4Q001F000A3Q0002001219000B000E3Q001219000C000F4Q004A000D000A3Q001219000E000F3Q000435000C005D00012Q00770010000F000A00123A001100103Q00201500110011001100201500120004000500201500133Q00050020150014000400052Q00490013001300142Q00220013001300102Q000F00120012001300201500130004000600201500143Q00060020150015000400062Q00490014001400152Q00220014001400102Q000F00130013001400201500140004000700201500153Q00070020150016000400072Q00490015001500162Q00220015001500102Q000F0014001400152Q00330011001400022Q0042001200024Q004A001300024Q003B00120002000100103C00030004001100123A001200123Q0020150012001200130020150012001200140020620012001200022Q004200145Q0020150014001400152Q00330012001400020006510012005800013Q0004253Q00580001002062001300120002001219001500164Q00330013001500020006510013005800013Q0004253Q0058000100201500130012001600103C00130004001100123A001300173Q0020150013001300182Q004A0014000B4Q003B001300020001000414000C002E000100103C000300043Q00123A000C00123Q002015000C000C0013002015000C000C0014002062000C000C00022Q0042000E5Q002015000E000E00152Q0033000C000E0002000651000C006E00013Q0004253Q006E0001002062000D000C0002001219000F00164Q0033000D000F0002000651000D006E00013Q0004253Q006E0001002015000D000C001600103C000D00044Q0042000D00014Q004A000E00024Q005D000F00014Q004F000D000F00012Q00043Q00017Q000F3Q00030A3Q006B657972656C65617365025Q0040524003043Q007461736B03043Q0077616974026Q33C33F03083Q006B65797072652Q73025Q00C05340029A5Q99B93F027B14AE47E17AB43F029A5Q99C93F025Q00C05140026Q00E03F03053Q007063612Q6C029A5Q99D93F026Q33D33F00554Q006B7Q00123A3Q00013Q001219000100024Q003B3Q0002000100123A3Q00033Q0020155Q0004001219000100054Q003B3Q0002000100123A3Q00063Q001219000100074Q003B3Q0002000100123A3Q00033Q0020155Q0004001219000100084Q003B3Q0002000100123A3Q00013Q001219000100074Q003B3Q0002000100123A3Q00033Q0020155Q0004001219000100094Q003B3Q0002000100123A3Q00063Q001219000100074Q003B3Q0002000100123A3Q00033Q0020155Q0004001219000100084Q003B3Q0002000100123A3Q00013Q001219000100074Q003B3Q0002000100123A3Q00033Q0020155Q00040012190001000A4Q003B3Q0002000100123A3Q00063Q0012190001000B4Q003B3Q0002000100123A3Q00033Q0020155Q0004001219000100084Q003B3Q0002000100123A3Q00013Q0012190001000B4Q003B3Q0002000100123A3Q00033Q0020155Q00040012190001000C4Q003B3Q0002000100123A3Q000D3Q00064C00013Q000100012Q001B3Q00014Q007B3Q0002000100123A000200033Q0020150002000200040012190003000E4Q003B00020002000100123A000200063Q0012190003000B4Q003B00020002000100123A000200033Q002015000200020004001219000300084Q003B00020002000100123A000200013Q0012190003000B4Q003B00020002000100123A000200033Q0020150002000200040012190003000F4Q003B0002000200012Q005D00026Q006B000200023Q00123A000200033Q0020150002000200040012190003000A4Q003B0002000200012Q0042000200033Q0006510002005400013Q0004253Q0054000100123A000200063Q001219000300024Q003B0002000200012Q00043Q00013Q00013Q00193Q0003093Q00506C6179657247756903043Q004D61696E03083Q004261636B7061636B03043Q004C697374030A3Q0047616D6570612Q73657303043Q0053652Q6C03073Q00412Q6472652Q73026Q007140030B3Q006D656D6F72795F7265616403053Q00666C6F6174026Q00104003043Q006D61746803053Q00666C2Q6F72026Q003440030C3Q006D6F7573656D6F766561627303043Q007461736B03043Q0077616974029A5Q99A93F026Q00F03F03063Q0072616E646F6D027Q00C0027Q0040027B14AE47E17AA43F029A5Q99B93F030B3Q006D6F75736531636C69636B00454Q00427Q0020155Q00010020155Q00020020155Q00030020155Q00040020155Q00050020155Q000600201500013Q000700206D00010001000800123A000200093Q0012190003000A4Q004A000400014Q003300020004000200123A000300093Q0012190004000A3Q00206D00050001000B2Q003300030005000200123A0004000C3Q00201500040004000D2Q004A000500024Q001000040002000200206D00040004000E00123A0005000C3Q00201500050005000D2Q004A000600034Q001000050002000200206D00050005000E00123A0006000F4Q004A000700044Q004A000800054Q004F00060008000100123A000600103Q002015000600060011001219000700124Q003B000600020001001219000600133Q0012190007000B3Q001219000800133Q0004350006003A000100123A000A000F3Q00123A000B000C3Q002015000B000B0014001219000C00153Q001219000D00164Q0033000B000D00022Q000F000B0004000B00123A000C000C3Q002015000C000C0014001219000D00153Q001219000E00164Q0033000C000E00022Q000F000C0005000C2Q004F000A000C000100123A000A00103Q002015000A000A0011001219000B00174Q003B000A0002000100041400060027000100123A0006000F4Q004A000700044Q004A000800054Q004F00060008000100123A000600103Q002015000600060011001219000700184Q003B00060002000100123A000600194Q00310006000100012Q00043Q00017Q000D3Q0003043Q0067616D65030A3Q004765745365727669636503053Q00537461747303103Q00506572666F726D616E6365537461747303053Q007061697273030B3Q004765744368696C6472656E03043Q004E616D6503083Q00496E7465726E616C03073Q0052752Q6E696E6703043Q007461736B03043Q0077616974026Q00F03F03053Q007063612Q6C00213Q00123A3Q00013Q0020625Q0002001219000200034Q00333Q000200020020155Q00042Q000600015Q00123A000200053Q00206200033Q00062Q004B000300044Q005500023Q00040004253Q000D00010020150007000600072Q001C0001000700060006530002000B000100020004253Q000B000100064C00023Q000100012Q002B3Q00014Q004200035Q0020150003000300080020150003000300090006510003002000013Q0004253Q0020000100123A0003000A3Q00201500030003000B0012190004000C4Q003B00030002000100123A0003000D3Q00064C00040001000100022Q001B3Q00014Q002B3Q00024Q003B0003000200010004253Q001100012Q00043Q00013Q00023Q00073Q002Q033Q004E2F4103073Q00412Q6472652Q73030B3Q006D656D6F72795F7265616403063Q00737472696E67026Q006A40028Q00026Q006B40011A4Q004200016Q0032000100013Q00067F00010006000100010004253Q00060001001219000200014Q0050000200023Q00201500020001000200123A000300033Q001219000400043Q00206D0005000200052Q00330003000500020006510003001100013Q0004253Q001100012Q0056000400033Q000E6500060011000100040004253Q001100012Q0050000300023Q00123A000400033Q001219000500043Q00206D0006000200072Q003300040006000200066C00050018000100040004253Q00180001001219000500014Q0050000500024Q00043Q00017Q00073Q0003063Q004D656D6F72792Q033Q0053657403083Q004D656D6F72793A202Q033Q0043505503053Q004350553A202Q033Q0047505503053Q004750553A20001C4Q00427Q0020155Q00010020625Q0002001219000200034Q0042000300013Q001219000400014Q00100003000200022Q005E0002000200032Q004F3Q000200012Q00427Q0020155Q00040020625Q0002001219000200054Q0042000300013Q001219000400044Q00100003000200022Q005E0002000200032Q004F3Q000200012Q00427Q0020155Q00060020625Q0002001219000200074Q0042000300013Q001219000400064Q00100003000200022Q005E0002000200032Q004F3Q000200012Q00043Q00017Q00033Q0003093Q00436861726163746572030A3Q006B657972656C65617365025Q0040524001174Q006B8Q004200015Q00067F00010016000100010004253Q001600012Q0042000100013Q0020150001000100010006510001001600013Q0004253Q0016000100123A000100023Q001219000200034Q003B0001000200012Q0042000100024Q00310001000100012Q0042000100034Q0042000200013Q0020150002000200012Q005D000300014Q004F0001000300012Q005D00016Q006B000100044Q0016000100014Q006B000100054Q00043Q00017Q00033Q0003093Q00436861726163746572030A3Q006B657972656C65617365025Q0040524000194Q00428Q00298Q006B8Q00427Q00067F3Q0018000100010004253Q001800012Q00423Q00013Q0020155Q00010006513Q001800013Q0004253Q0018000100123A3Q00023Q001219000100034Q003B3Q000200012Q00423Q00024Q00313Q000100012Q00423Q00034Q0042000100013Q0020150001000100012Q005D000200014Q004F3Q000200012Q005D8Q006B3Q00044Q00168Q006B3Q00054Q00043Q00019Q002Q002Q014Q00043Q00019Q002Q0001064Q006B8Q0042000100024Q004200026Q00320001000100022Q006B000100014Q00043Q00019Q002Q0001024Q006B8Q00043Q00019Q002Q0001024Q006B8Q00043Q00019Q002Q0001024Q006B8Q00043Q00019Q002Q0001064Q006B8Q0042000100014Q00310001000100012Q000600016Q006B000100024Q00043Q00017Q00033Q0003063Q0069706169727303053Q007461626C6503063Q00696E73657274011E4Q006B8Q000600015Q00123A000200014Q004200036Q007B0002000200040004253Q000B000100123A000700023Q0020150007000700032Q004A000800014Q004A000900064Q004F00070009000100065300020006000100020004253Q0006000100123A000200014Q0042000300014Q007B0002000200040004253Q0016000100123A000700023Q0020150007000700032Q004A000800014Q004A000900064Q004F00070009000100065300020011000100020004253Q001100012Q006B000100024Q0042000200034Q00310002000100012Q000600026Q006B000200044Q00043Q00017Q00033Q0003063Q0069706169727303053Q007461626C6503063Q00696E73657274011E4Q006B8Q000600015Q00123A000200014Q0042000300014Q007B0002000200040004253Q000B000100123A000700023Q0020150007000700032Q004A000800014Q004A000900064Q004F00070009000100065300020006000100020004253Q0006000100123A000200014Q004200036Q007B0002000200040004253Q0016000100123A000700023Q0020150007000700032Q004A000800014Q004A000900064Q004F00070009000100065300020011000100020004253Q001100012Q006B000100024Q0042000200034Q00310002000100012Q000600026Q006B000200044Q00043Q00017Q00013Q002Q033Q0053657400224Q00068Q006B8Q00068Q006B3Q00014Q00068Q006B3Q00024Q00068Q006B3Q00034Q00423Q00043Q0006513Q000F00013Q0004253Q000F00012Q00423Q00043Q0020625Q00012Q000600026Q004F3Q000200012Q00423Q00053Q0006513Q001600013Q0004253Q001600012Q00423Q00053Q0020625Q00012Q000600026Q004F3Q000200012Q00423Q00063Q0006513Q001D00013Q0004253Q001D00012Q00423Q00063Q0020625Q00012Q000600026Q004F3Q000200012Q00423Q00074Q00313Q000100012Q00068Q006B3Q00084Q00043Q00019Q002Q0001064Q006B8Q004200016Q0042000200024Q00770001000100022Q006B000100014Q00043Q00017Q00023Q002Q033Q00536574026Q00084000054Q00427Q0020625Q0001001219000200024Q004F3Q000200012Q00043Q00019Q002Q0001024Q006B8Q00043Q00017Q00023Q002Q033Q00536574027Q004000054Q00427Q0020625Q0001001219000200024Q004F3Q000200012Q00043Q00019Q002Q0001024Q006B8Q00043Q00017Q00023Q002Q033Q00536574026Q00444000054Q00427Q0020625Q0001001219000200024Q004F3Q000200012Q00043Q00019Q002Q0001064Q006B8Q0042000100024Q004200026Q00770001000100022Q006B000100014Q00043Q00017Q00023Q002Q033Q00536574026Q003E4000054Q00427Q0020625Q0001001219000200024Q004F3Q000200012Q00043Q00017Q00023Q0003043Q007461736B03053Q00737061776E00083Q00123A3Q00013Q0020155Q000200064C00013Q000100032Q001B8Q001B3Q00014Q001B3Q00024Q003B3Q000200012Q00043Q00013Q00018Q00054Q00428Q0042000100014Q0042000200024Q004F3Q000200012Q00043Q00017Q00023Q0003043Q007461736B03053Q00737061776E00063Q00123A3Q00013Q0020155Q000200064C00013Q000100012Q001B8Q003B3Q000200012Q00043Q00013Q00013Q00153Q0003093Q00776F726B7370616365030E3Q0046696E6446697273744368696C642Q033Q004D617003063Q00646562726973030E3Q0047657444657363656E64616E7473026Q00F03F2Q033Q0049734103083Q004261736550617274030A3Q0043616E436F2Q6C696465010003053Q007063612Q6C03063Q00506172656E74025Q00408F40028Q0003043Q007461736B03043Q007761697403093Q0043686172616374657203063Q0069706169727303043Q0047616D6503053Q00547562657303043Q004E616D6500503Q00123A3Q00013Q0020625Q0002001219000200034Q00333Q0002000200123A000100013Q002062000100010002001219000300044Q00330001000300020006513Q002600013Q0004253Q002600010006510001002600013Q0004253Q0026000100206200023Q00052Q0010000200020002001219000300064Q0056000400023Q001219000500063Q0004350003002600012Q0032000700020006002062000800070007001219000A00084Q00330008000A00020006510008001E00013Q0004253Q001E000100304400070009000A00123A0008000B3Q00064C00093Q000100012Q002B3Q00074Q003B00080002000100103C0007000C000100202E00080006000D002657000800240001000E0004253Q0024000100123A0008000F3Q0020150008000800102Q00310008000100012Q005800075Q0004140003001200012Q004200025Q0020150002000200110006510002003900013Q0004253Q0039000100123A000200124Q004200035Q0020150003000300110020620003000300052Q004B000300044Q005500023Q00040004253Q00370001002062000700060007001219000900084Q00330007000900020006510007003700013Q0004253Q0037000100304400060009000A00065300020031000100020004253Q0031000100123A000200013Q0020150002000200130020150002000200140020620002000200022Q004200045Q0020150004000400152Q00330002000400020006510002004F00013Q0004253Q004F000100123A000300123Q0020620004000200052Q004B000400054Q005500033Q00050004253Q004D0001002062000800070007001219000A00084Q00330008000A00020006510008004D00013Q0004253Q004D000100304400070009000A00065300030047000100020004253Q004700012Q00043Q00013Q00013Q00033Q0003083Q0043616E5175657279010003083Q0043616E546F75636800054Q00427Q0030443Q000100022Q00427Q0030443Q000300022Q00043Q00017Q00013Q0003063Q00546F2Q676C6500044Q00427Q0020625Q00012Q003B3Q000200012Q00043Q00019Q002Q002Q014Q00043Q00017Q001B3Q0003043Q007461736B03043Q0077616974026Q00E03F03093Q00776F726B737061636503043Q0047616D6503043Q0046697368030E3Q0046696E6446697273744368696C6403063Q00636C69656E7403093Q0043686172616374657203103Q0048756D616E6F6964522Q6F745061727403083Q00506F736974696F6E024Q007E842E41028Q0003063Q00697061697273030B3Q004765744368696C6472656E026Q00F03F03043Q004E616D6503043Q004865616403083Q00522Q6F7450617274030B3Q005072696D6172795061727403013Q005803013Q005903013Q005A03043Q006D61746803043Q0073717274026Q003E4003053Q007063612Q6C007F3Q00123A3Q00013Q0020155Q0002001219000100034Q003B3Q000200012Q00427Q0006515Q00013Q0004255Q00012Q00423Q00013Q00067F5Q000100010004255Q00012Q00423Q00023Q0006513Q000E00013Q0004253Q000E00010004255Q000100123A3Q00043Q0020155Q00050020155Q00060006513Q001900013Q0004253Q0019000100123A3Q00043Q0020155Q00050020155Q00060020625Q0007001219000200084Q00333Q0002000200067F3Q001C000100010004253Q001C00010004255Q00012Q0042000100033Q00201500010001000900060B00020023000100010004253Q002300010020620002000100070012190004000A4Q003300020004000200067F00020026000100010004253Q002600010004255Q000100201500030002000B2Q0016000400043Q0012190005000C3Q0012190006000D3Q00123A0007000E3Q00206200083Q000F2Q004B000800094Q005500073Q00090004253Q0068000100206D0006000600102Q0042000C00043Q002015000D000B00112Q0032000C000C000D00067F000C0062000100010004253Q006200012Q0042000C00054Q004A000D000B4Q0010000C00020002000651000C006200013Q0004253Q00620001002062000C000B0007001219000E00124Q0033000C000E000200067F000C0045000100010004253Q00450001002062000C000B0007001219000E00134Q0033000C000E000200067F000C0045000100010004253Q00450001002015000C000B0014000651000C006200013Q0004253Q00620001002015000D000C000B000651000D006200013Q0004253Q00620001002015000D000C000B002015000D000D0015002015000E000300152Q0049000D000D000E002015000E000C000B002015000E000E0016002015000F000300162Q0049000E000E000F002015000F000C000B002015000F000F00170020150010000300172Q0049000F000F001000123A001000183Q0020150010001000192Q00220011000D000D2Q00220012000E000E2Q000F0011001100122Q00220012000F000F2Q000F0011001100122Q001000100002000200062800100062000100050004253Q006200012Q004A000500104Q004A0004000B3Q00202E000C0006001A002657000C00680001000D0004253Q0068000100123A000C00013Q002015000C000C00022Q0031000C000100010006530007002F000100020004253Q002F00012Q005D00075Q00123A0008001B3Q00064C00093Q000100052Q001B3Q00034Q001B3Q00064Q002B3Q00074Q001B3Q00074Q001B3Q00084Q003B00080002000100067F00070077000100010004253Q007700012Q006B000400093Q0004253Q007900012Q0016000800084Q006B000800094Q00587Q0004255Q00012Q00587Q0004255Q00010004255Q00012Q00043Q00013Q00013Q00093Q0003093Q00506C6179657247756903043Q004D61696E030E3Q0046696E6446697273744368696C6403063Q004F787967656E03083Q00746F6E756D626572030C3Q00476574412Q7472696275746503093Q006F6C646F787967656E026Q005940029Q00224Q00427Q0020155Q00010020155Q00020020625Q0003001219000200044Q00333Q000200020006513Q002100013Q0004253Q0021000100123A000100053Q00206200023Q0006001219000400074Q0078000200044Q001F00013Q000200067F00010010000100010004253Q00100001001219000100084Q0042000200013Q000E6500090016000100020004253Q001600012Q0042000200013Q00067F00020017000100010004253Q00170001001219000200084Q00770003000100020020680003000300082Q0042000400034Q0042000500044Q000F00040004000500063F00030002000100040004253Q001F00012Q008000046Q005D000400014Q006B000400024Q00043Q00017Q00053Q00028Q0003043Q007461736B03043Q0077616974029A5Q99A93F03053Q007063612Q6C00253Q0012193Q00013Q00123A000100023Q002015000100010003001219000200044Q003B0001000200012Q004200015Q0006510001000900013Q0004253Q000900010004253Q000100012Q0042000100013Q0006510001001500013Q0004253Q001500012Q0042000100023Q0006510001001500013Q0004253Q001500010012193Q00013Q00123A000100053Q00064C00023Q000100012Q001B3Q00024Q003B0001000200010004253Q000100012Q0042000100013Q0006510001000100013Q0004253Q000100012Q0042000100023Q00067F00010001000100010004253Q000100012Q0042000100033Q00067F00010001000100010004253Q0001000100123A000100053Q00064C00020001000100022Q001B3Q00044Q002B8Q003B0001000200010004253Q000100012Q00043Q00013Q00023Q00083Q00030E3Q0046696E6446697273744368696C6403043Q004865616403083Q00522Q6F7450617274030B3Q005072696D6172795061727403093Q00776F726B7370616365030D3Q0043752Q72656E7443616D65726103063Q006C2Q6F6B417403083Q00506F736974696F6E00194Q00427Q0020625Q0001001219000200024Q00333Q0002000200067F3Q000E000100010004253Q000E00012Q00427Q0020625Q0001001219000200034Q00333Q0002000200067F3Q000E000100010004253Q000E00012Q00427Q0020155Q00040006513Q001800013Q0004253Q0018000100123A000100053Q00201500010001000600201500010001000700123A000200053Q00201500020002000600201500020002000800201500033Q00082Q004F0001000300012Q00043Q00017Q00113Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F7450617274026Q00F03F025Q0080764003043Q006D6174682Q033Q00726164026Q00344003083Q00506F736974696F6E03073Q00566563746F72332Q033Q006E65772Q033Q00636F73028Q002Q033Q0073696E03093Q00776F726B7370616365030D3Q0043752Q72656E7443616D65726103063Q006C2Q6F6B4174002C4Q00427Q0020155Q000100060B0001000700013Q0004253Q0007000100206200013Q0002001219000300034Q003300010003000200067F0001000A000100010004253Q000A00012Q00043Q00014Q0042000200013Q00206D00020002000400202E0002000200052Q006B000200013Q00123A000200063Q0020150002000200072Q0042000300014Q0010000200020002001219000300083Q00201500040001000900123A0005000A3Q00201500050005000B00123A000600063Q00201500060006000C2Q004A000700024Q00100006000200022Q00220006000600030012190007000D3Q00123A000800063Q00201500080008000E2Q004A000900024Q00100008000200022Q00220008000800032Q00330005000800022Q000F00040004000500123A0005000F3Q00201500050005001000201500050005001100123A0006000F3Q0020150006000600100020150006000600092Q004A000700044Q004F0005000700012Q00043Q00017Q00043Q0003043Q007461736B03043Q0077616974026Q00F03F03053Q007063612Q6C00103Q00123A3Q00013Q0020155Q0002001219000100034Q003B3Q000200012Q00427Q0006515Q00013Q0004255Q00012Q00423Q00013Q00067F5Q000100010004255Q000100123A3Q00043Q00064C00013Q000100012Q001B3Q00024Q007B3Q000200010004255Q00012Q00043Q00013Q00013Q000F3Q0003093Q00506C6179657247756903043Q004D61696E030B3Q004361746368696E6742617203053Q004672616D652Q033Q0042617203053Q00436174636803053Q0047722Q656E03073Q00412Q6472652Q73030C3Q006D656D6F72795F777269746503053Q00666C6F6174025Q00A09440026Q00F03F025Q00B09440025Q00C09440025Q00D0944000204Q00427Q0020155Q00010020155Q00020020155Q00030020155Q00040020155Q000500201500013Q00060020150001000100070020150001000100080006510001001F00013Q0004253Q001F000100123A000200093Q0012190003000A3Q00206D00040001000B0012190005000C4Q004F00020005000100123A000200093Q0012190003000A3Q00206D00040001000D0012190005000C4Q004F00020005000100123A000200093Q0012190003000A3Q00206D00040001000E0012190005000C4Q004F00020005000100123A000200093Q0012190003000A3Q00206D00040001000F0012190005000C4Q004F0002000500012Q00043Q00017Q00233Q00028Q0003043Q007461736B03043Q0077616974029A5Q99B93F029A5Q99C93F03083Q006B65797072652Q73025Q0040524003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403093Q00506C6179657247756903043Q004D61696E03063Q004F787967656E03083Q00746F6E756D626572030C3Q00476574412Q7472696275746503093Q006F6C646F787967656E026Q005940025Q0080584003053Q00737061776E03093Q00776F726B737061636503043Q0047616D6503043Q004669736803063Q00636C69656E7403063Q00506172656E7403083Q00522Q6F745061727403043Q004865616403083Q00506F736974696F6E03013Q005803013Q005903013Q005A03043Q006D61746803043Q0073717274026Q00144003053Q007063612Q6C030B3Q006D6F75736531636C69636B00CD3Q001219000100013Q00123A000200023Q002015000200020003001219000300044Q003B0002000200012Q004200025Q0006510002000E00013Q0004253Q000E00012Q0042000200013Q00067F0002000E000100010004253Q000E00012Q0042000200023Q0006510002001E00013Q0004253Q001E00012Q0042000200023Q0006510002000100013Q0004253Q000100012Q0042000200023Q0006510002001900013Q0004253Q0019000100123A000200023Q002015000200020003001219000300044Q003B0002000200010004253Q0011000100123A000200023Q002015000200020003001219000300054Q003B0002000200010004253Q0001000100123A000200063Q001219000300074Q003B0002000200012Q0042000200033Q00201500020002000800060B00030028000100020004253Q002800010020620003000200090012190005000A4Q003300030005000200067F0003002B000100010004253Q002B00010004253Q000100012Q0042000400033Q00201500040004000B00201500040004000C0020620004000400090012190006000D4Q00330004000600020006510004003A00013Q0004253Q003A000100123A0005000E3Q00206200060004000F001219000800104Q0078000600084Q001F00053Q000200067F0005003B000100010004253Q003B0001001219000500114Q0042000600043Q0006280006003F000100050004253Q003F00012Q006B000500044Q0042000600043Q000E6500010045000100060004253Q004500012Q0042000600043Q00067F00060046000100010004253Q00460001001219000600114Q00770007000500060020680007000700110006510004005300013Q0004253Q005300012Q0042000800053Q00062A00070053000100080004253Q005300012Q0042000800063Q00067F00080053000100010004253Q005300012Q005D000800014Q006B000800063Q0004253Q00610001000E5A00120061000100070004253Q006100012Q0042000800063Q0006510008006100013Q0004253Q006100012Q005D00086Q006B000800064Q0042000800073Q0006510008006100013Q0004253Q006100012Q005D000800014Q006B000800024Q0042000800084Q00310008000100012Q0042000800063Q0006510008007100013Q0004253Q007100012Q0016000800084Q006B000800093Q00123A000800023Q00201500080008001300064C00093Q000100052Q001B3Q000A4Q002B3Q00034Q001B3Q000B4Q001B3Q000C4Q001B3Q000D4Q003B0008000200012Q005800025Q0004253Q0001000100123A000800143Q00201500080008001500201500080008001600201500080008001700067F00080079000100010004253Q007900012Q005800025Q0004253Q000100012Q0042000900093Q000651000900C600013Q0004253Q00C60001002015000A00090018000651000A00C600013Q0004253Q00C60001002062000A00090009001219000C000A4Q0033000A000C000200067F000A008C000100010004253Q008C0001002062000A00090009001219000C00194Q0033000A000C000200067F000A008C000100010004253Q008C0001002062000A00090009001219000C001A4Q0033000A000C0002000651000A00C700013Q0004253Q00C70001002015000B000A001B002015000C000B001C002015000D0003001B002015000D000D001C2Q0049000C000C000D002015000D000B001D002015000E0003001B002015000E000E001D2Q0049000D000D000E002015000E000B001E002015000F0003001B002015000F000F001E2Q0049000E000E000F00123A000F001F3Q002015000F000F00202Q00220010000C000C2Q00220011000D000D2Q000F0010001000112Q00220011000E000E2Q000F0010001000112Q0010000F000200022Q0042001000054Q00420011000E4Q000F00100010001100063F00070002000100100004253Q00A900012Q008000106Q005D001000014Q00420011000F3Q000628001100B80001000F0004253Q00B8000100067F001000B8000100010004253Q00B8000100123A001100023Q00201500110011001300064C00120001000100042Q001B3Q000A4Q002B3Q00034Q002B3Q00094Q001B3Q000F4Q003B0011000200010004253Q00C7000100067F001000C7000100010004253Q00C7000100123A0011001F3Q0020150011001100202Q00220012000C000C2Q00220013000E000E2Q000F0012001200132Q0010001100020002000E65002100C7000100110004253Q00C7000100123A001100223Q00123A001200234Q003B0011000200010004253Q00C700012Q00168Q005800025Q0004253Q000100012Q005800025Q0004253Q000100010004253Q000100012Q00043Q00013Q00023Q00023Q00026Q004E4003083Q00536166655A6F6E65000C4Q00428Q0042000100013Q00064C00023Q000100012Q001B3Q00024Q0016000300033Q001219000400014Q0042000500034Q0042000600044Q0077000500050006001219000600024Q004F3Q000600012Q00043Q00013Q00018Q00034Q00428Q00503Q00024Q00043Q00017Q00013Q0003043Q004E616D65000D4Q00428Q0042000100013Q00064C00023Q000100012Q001B3Q00023Q00064C00030001000100032Q001B3Q00024Q001B3Q00034Q001B3Q00014Q0016000400054Q0042000600023Q0020150006000600012Q004F3Q000600012Q00043Q00013Q00023Q000C3Q0003063Q00506172656E74030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403083Q00522Q6F745061727403043Q004865616403073Q00566563746F72332Q033Q006E657703083Q00506F736974696F6E03013Q0058026Q00244003013Q005903013Q005A00274Q00427Q0006513Q002400013Q0004253Q002400012Q00427Q0020155Q00010006513Q002400013Q0004253Q002400012Q00427Q0020625Q0002001219000200034Q00333Q0002000200067F3Q0017000100010004253Q001700012Q00427Q0020625Q0002001219000200044Q00333Q0002000200067F3Q0017000100010004253Q001700012Q00427Q0020625Q0002001219000200054Q00333Q000200020006513Q002400013Q0004253Q0024000100123A000100063Q00201500010001000700201500023Q000800201500020002000900206D00020002000A00201500033Q000800201500030003000B00201500043Q000800201500040004000C2Q0002000100044Q007000016Q00168Q00503Q00024Q00043Q00017Q00093Q00030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403083Q00522Q6F745061727403043Q004865616403043Q006D6174682Q033Q0061627303083Q00506F736974696F6E03013Q0059026Q002040012D4Q004200015Q0006510001001300013Q0004253Q001300012Q004200015Q002062000100010001001219000300024Q003300010003000200067F00010013000100010004253Q001300012Q004200015Q002062000100010001001219000300034Q003300010003000200067F00010013000100010004253Q001300012Q004200015Q002062000100010001001219000300044Q00330001000300020006510001002600013Q0004253Q002600012Q0042000200013Q00062A3Q0023000100020004253Q0023000100123A000200053Q0020150002000200062Q0042000300023Q0020150003000300070020150003000300080020150004000100070020150004000400082Q00490003000300042Q001000020002000200264300020024000100090004253Q002400012Q008000026Q005D000200014Q0050000200024Q0042000200013Q00063F3Q0002000100020004253Q002A00012Q008000026Q005D000200014Q0050000200024Q00043Q00017Q00", GetFEnv(), ...);