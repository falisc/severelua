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
											local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
											Top = (Limit + A) - 1;
											local Edx = 0;
											for Idx = A, Top do
												Edx = Edx + 1;
												Stk[Idx] = Results[Edx];
											end
										else
											local B = Inst[3];
											local K = Stk[B];
											for Idx = B + 1, Inst[4] do
												K = K .. Stk[Idx];
											end
											Stk[Inst[2]] = K;
										end
									elseif (Enum > 2) then
										local A = Inst[2];
										local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
										local Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
									else
										Stk[Inst[2]] = Env[Inst[3]];
									end
								elseif (Enum <= 5) then
									if (Enum > 4) then
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
								elseif (Enum > 6) then
									Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
								else
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								end
							elseif (Enum <= 11) then
								if (Enum <= 9) then
									if (Enum == 8) then
										if (Stk[Inst[2]] == Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Inst[2] < Stk[Inst[4]]) then
										VIP = Inst[3];
									else
										VIP = VIP + 1;
									end
								elseif (Enum == 10) then
									if (Stk[Inst[2]] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 13) then
								if (Enum == 12) then
									local B = Stk[Inst[4]];
									if B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
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
							elseif (Enum > 14) then
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							else
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 23) then
							if (Enum <= 19) then
								if (Enum <= 17) then
									if (Enum == 16) then
										if (Stk[Inst[2]] <= Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										Stk[Inst[2]] = Inst[3] / Stk[Inst[4]];
									end
								elseif (Enum > 18) then
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
										if (Mvm[1] == 103) then
											Indexes[Idx - 1] = {Stk,Mvm[3]};
										else
											Indexes[Idx - 1] = {Upvalues,Mvm[3]};
										end
										Lupvals[#Lupvals + 1] = Indexes;
									end
									Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
								else
									Stk[Inst[2]] = {};
								end
							elseif (Enum <= 21) then
								if (Enum > 20) then
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
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								end
							elseif (Enum == 22) then
								Stk[Inst[2]] = #Stk[Inst[3]];
							else
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							end
						elseif (Enum <= 27) then
							if (Enum <= 25) then
								if (Enum == 24) then
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
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
							elseif (Enum == 26) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
							elseif (Stk[Inst[2]] ~= Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 29) then
							if (Enum == 28) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							else
								Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
							end
						elseif (Enum > 30) then
							Stk[Inst[2]] = not Stk[Inst[3]];
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
					elseif (Enum <= 47) then
						if (Enum <= 39) then
							if (Enum <= 35) then
								if (Enum <= 33) then
									if (Enum > 32) then
										do
											return Stk[Inst[2]];
										end
									else
										local A = Inst[2];
										do
											return Stk[A](Unpack(Stk, A + 1, Inst[3]));
										end
									end
								elseif (Enum == 34) then
									do
										return Stk[Inst[2]];
									end
								elseif (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 37) then
								if (Enum > 36) then
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								elseif (Stk[Inst[2]] < Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 38) then
								if (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Stk[Inst[2]] > Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = VIP + Inst[3];
							end
						elseif (Enum <= 43) then
							if (Enum <= 41) then
								if (Enum > 40) then
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
									local Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum == 42) then
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
							else
								Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
							end
						elseif (Enum <= 45) then
							if (Enum == 44) then
								Stk[Inst[2]] = not Stk[Inst[3]];
							else
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							end
						elseif (Enum > 46) then
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 55) then
						if (Enum <= 51) then
							if (Enum <= 49) then
								if (Enum > 48) then
									Stk[Inst[2]] = Env[Inst[3]];
								else
									do
										return;
									end
								end
							elseif (Enum == 50) then
								if (Stk[Inst[2]] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							end
						elseif (Enum <= 53) then
							if (Enum == 52) then
								Stk[Inst[2]][Inst[3]] = Inst[4];
							else
								Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
							end
						elseif (Enum > 54) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum <= 59) then
						if (Enum <= 57) then
							if (Enum == 56) then
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
									if (Mvm[1] == 103) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							else
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							end
						elseif (Enum == 58) then
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						else
							Stk[Inst[2]] = Inst[3] ~= 0;
						end
					elseif (Enum <= 61) then
						if (Enum == 60) then
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
						end
					elseif (Enum <= 62) then
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
					elseif (Enum > 63) then
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
						local B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
					end
				elseif (Enum <= 97) then
					if (Enum <= 80) then
						if (Enum <= 72) then
							if (Enum <= 68) then
								if (Enum <= 66) then
									if (Enum == 65) then
										local A = Inst[2];
										local Results = {Stk[A](Stk[A + 1])};
										local Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
									else
										local A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								elseif (Enum == 67) then
									Stk[Inst[2]] = Stk[Inst[3]];
								elseif (Stk[Inst[2]] < Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 70) then
								if (Enum > 69) then
									local B = Stk[Inst[4]];
									if not B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								else
									do
										return;
									end
								end
							elseif (Enum == 71) then
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
							elseif (Stk[Inst[2]] > Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 76) then
							if (Enum <= 74) then
								if (Enum == 73) then
									local A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
								else
									Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
								end
							elseif (Enum == 75) then
								Stk[Inst[2]] = Inst[3] / Stk[Inst[4]];
							else
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							end
						elseif (Enum <= 78) then
							if (Enum == 77) then
								if (Stk[Inst[2]] > Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Inst[2] < Stk[Inst[4]]) then
								VIP = Inst[3];
							else
								VIP = VIP + 1;
							end
						elseif (Enum > 79) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						else
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum <= 88) then
						if (Enum <= 84) then
							if (Enum <= 82) then
								if (Enum == 81) then
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								else
									Stk[Inst[2]]();
								end
							elseif (Enum == 83) then
								VIP = Inst[3];
							else
								Upvalues[Inst[3]] = Stk[Inst[2]];
							end
						elseif (Enum <= 86) then
							if (Enum == 85) then
								if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
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
						elseif (Enum == 87) then
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
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum <= 92) then
						if (Enum <= 90) then
							if (Enum == 89) then
								Upvalues[Inst[3]] = Stk[Inst[2]];
							else
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							end
						elseif (Enum == 91) then
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
						else
							Stk[Inst[2]] = #Stk[Inst[3]];
						end
					elseif (Enum <= 94) then
						if (Enum > 93) then
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
						else
							Stk[Inst[2]] = Inst[3] ~= 0;
						end
					elseif (Enum <= 95) then
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum > 96) then
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
				elseif (Enum <= 113) then
					if (Enum <= 105) then
						if (Enum <= 101) then
							if (Enum <= 99) then
								if (Enum > 98) then
									local A = Inst[2];
									do
										return Unpack(Stk, A, A + Inst[3]);
									end
								elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 100) then
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							else
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							end
						elseif (Enum <= 103) then
							if (Enum > 102) then
								Stk[Inst[2]] = Stk[Inst[3]];
							else
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							end
						elseif (Enum == 104) then
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
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						end
					elseif (Enum <= 109) then
						if (Enum <= 107) then
							if (Enum > 106) then
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							else
								Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
							end
						elseif (Enum == 108) then
							Stk[Inst[2]]();
						elseif Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 111) then
						if (Enum == 110) then
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
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
					elseif (Enum == 112) then
						if (Stk[Inst[2]] == Inst[4]) then
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
				elseif (Enum <= 121) then
					if (Enum <= 117) then
						if (Enum <= 115) then
							if (Enum == 114) then
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							elseif not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 116) then
							local B = Stk[Inst[4]];
							if not B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						elseif (Inst[2] <= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 119) then
						if (Enum > 118) then
							local A = Inst[2];
							local T = Stk[A];
							local B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						else
							local B = Inst[3];
							local K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
						end
					elseif (Enum == 120) then
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
					else
						local A = Inst[2];
						local T = Stk[A];
						for Idx = A + 1, Inst[3] do
							Insert(T, Stk[Idx]);
						end
					end
				elseif (Enum <= 125) then
					if (Enum <= 123) then
						if (Enum == 122) then
							VIP = Inst[3];
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						end
					elseif (Enum > 124) then
						local A = Inst[2];
						Stk[A] = Stk[A]();
					elseif (Inst[2] <= Stk[Inst[4]]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 127) then
					if (Enum == 126) then
						Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
					elseif (Stk[Inst[2]] > Stk[Inst[4]]) then
						VIP = VIP + 1;
					else
						VIP = VIP + Inst[3];
					end
				elseif (Enum <= 128) then
					Stk[Inst[2]][Inst[3]] = Inst[4];
				elseif (Enum > 129) then
					if (Stk[Inst[2]] ~= Inst[4]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				else
					Stk[Inst[2]] = Upvalues[Inst[3]];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!05012Q0003043Q0067616D65030A3Q004765745365727669636503073Q00506C6179657273030B3Q004C6F63616C506C6179657203103Q0055736572496E7075745365727669636503053Q007072696E74031C3Q005B4162792Q73616C5D20536372697074207374617274696E673Q2E030E3Q00466F72676F2Q74656E20442Q657003073Q00566563746F72332Q033Q006E6577021F85EB51B8FE57C002F853E3A51B10B3402Q022B8716D90E27C0030D3Q00416E6369656E742053616E6473024Q33B3E09BC002B81E85EB912DB14002FCA9F1D24DA22F40030C3Q0053756E6B656E2057696C647302736891ED7C40ADC0024Q33731DA340026891ED7CFFB2B3C0030C3Q0053706972697420522Q6F74730248E17A14AEFE994002378941602583AF4002F6285C8FC2E59DC0031D3Q005B4162792Q73616C5D2044656661756C74206661726D20617265613A20028Q00026Q005440026Q002440026Q000840027Q0040026Q003940026Q003E40031E3Q005B4162792Q73616C5D2053652Q74696E677320696E697469616C697A656403223Q005B4162792Q73616C5D3Q206F78795468726573686F6C6450657263656E74203D20031C3Q005B4162792Q73616C5D3Q2074772Q656E4475726174696F6E203D2003163Q005B4162792Q73616C5D3Q206D696E44697374203D2003193Q005B4162792Q73616C5D2048656C7065727320646566696E656403213Q005B4162792Q73616C5D204D6F76656D656E7420656E67696E6520646566696E6564031F3Q005B4162792Q73616C5D204C6F6164696E67205549206C6962726172793Q2E030A3Q006C6F6164737472696E6703073Q00482Q747047657403443Q00682Q7470733A2Q2F7261772E67697468756275736572636F6E74656E742E636F6D2F7A2Q652D373635342F55492F726566732F68656164732F6D61696E2F55492E6C756103223Q005B4162792Q73616C5D205549206C696272617279206C6F616465642C205549203D2003083Q00746F737472696E6703023Q00554903063Q006E6F74696679030C3Q004162792Q73616C204D656E7503093Q005549204C6F6164656403063Q0057696E646F7703053Q005469746C6503243Q004162792Q73616C204D656E75207C204275696C643A20416C706861207C204D617463686103043Q0053697A6503073Q00566563746F7232025Q00407F40025Q00E0754003043Q004F70656E2Q0103053Q005468656D6503063Q00476C6F62616C030B3Q004C69676874412Q63656E7403063Q00436F6C6F723303073Q0066726F6D524742026Q005940026Q006940025Q00E06F4003063Q00412Q63656E74026Q004940026Q005E40025Q00806B40030A3Q004461726B412Q63656E74025Q00805140025Q00C0624003093Q004C6967687442617365026Q002E40026Q003440025Q0080464003043Q0042617365026Q00284003083Q004461726B42617365026Q001440026Q00184003043Q0054657874026Q006E4003083Q00436F2Q6C61707365026Q00644003063Q00436F726E657203073Q0050612Q64696E6703173Q005B4162792Q73616C5D205468656D6520612Q706C69656403183Q005B4162792Q73616C5D2057696E646F7720637265617465642Q033Q0054616203043Q00486F6D6503073Q0053656374696F6E03043Q00496E666F03053Q004C6162656C03253Q0048652Q6C6F2C207468616E6B20796F7520666F72207573696E67206D79207363726970742E03173Q004D616465206279204070746163756E6974202F2066616C03303Q00646D204070746163756E697420666F7220616E7920692Q73756573202F2062756773202F2073752Q67657374696F6E7303083Q00496E7465726E616C03093Q00436F2Q6C617073656403113Q00506572666F726D616E636520537461747303063Q004D656D6F7279030A3Q004D656D6F72793A202Q2D2Q033Q0043505503073Q004350553A202Q2D2Q033Q0047505503073Q004750553A202Q2D031A3Q005B4162792Q73616C5D20486F6D6520746162206372656174656403043Q007461736B03053Q00737061776E03073Q004661726D696E6703093Q004175746F204661726D03253Q005B4162792Q73616C5D204661726D696E67207461622F73656374696F6E206372656174656403083Q00436865636B626F7803063Q00456E61626C6503073Q0044656661756C74010003073Q004B657962696E64030F3Q00546F2Q676C65204175746F6661726D2Q033Q004B657903043Q00456E756D03073Q004B6579436F646503013Q005003053Q00706169727303053Q007461626C6503063Q00696E73657274031C3Q005B4162792Q73616C5D204C6F636174696F6E2063686F696365733A2003063Q00636F6E63617403023Q002C2003083Q0044726F70646F776E03093Q004661726D204172656103073Q004F7074696F6E7303063Q00536C6964657203103Q004F787967656E205468726573686F6C642Q033Q004D696E2Q033Q004D617803043Q005374657003063Q0053752Q66697803013Q002503153Q004F787967656E205761726E696E672042752Q666572026Q00F03F03273Q005B4162792Q73616C5D204661726D696E672073656374696F6E207769646765747320612Q64656403053Q00437570696403063Q004C6F6E656C7903053Q005368696E7903043Q00502Q6F7003043Q00526F636B03053Q00436F72616C03043Q004D6F2Q7303053Q004D6574616C03043Q0053616E6403063Q00416C62696E6F030B3Q005472616E73706172656E7403063Q0043616374757303063Q0053706972697403063Q00466F2Q73696C03063Q00476F6C64656E03083Q004E6567617469766503053Q00466169727903093Q00496E76697369626C6503043Q004E656F6E030B3Q00556C74726176696F6C657403063Q00522Q6F74656403063Q00536861646F7703073Q00416E67656C696303073Q004162792Q73616C03083Q0047726F756E64656403063Q0042616E616E6103043Q004A61646503063Q004C6971756964030B3Q00466973682046696C74657203283Q0053656C656374206D75746174696F6E7320746F207461726765742028656D707479203D20612Q6C29030D3Q004D756C746944726F70646F776E03093Q004D75746174696F6E7303293Q0053656C656374206669736820747970657320746F207461726765742028656D707479203D20612Q6C29030C3Q00466973682054797065732031030D3Q00416E6369656E7420536861726B030A3Q00416E676C65726669736803093Q0042612Q726163756461030C3Q004269676D6F75746866697368030D3Q00426C61636B66696E2054756E6103083Q00426C6F626669736803093Q00426C75652054616E67030C3Q00426C756566696E2054756E6103083Q00436176656669736803093Q00436C6F776E666973682Q033Q00436F6403063Q00446973637573030A3Q00447261676F6E6669736803073Q004579656669736803073Q0047726F75706572030C3Q0048612Q6D657220536861726B03133Q00496E666C617465642050752Q66657266697368030C3Q004A616775617220536861726B03093Q004A652Q6C7966697368030F3Q004B696E6720416E676C65726669736803083Q004C696F6E6669736803093Q004D616869204D616869030C3Q00466973682054797065732032030A3Q004D6F736173617572757303083Q004E61706F6C656F6E03073Q004E61727768616C030F3Q00506163696669632046616E66697368030B3Q0050656C6963616E2045656C03073Q00506972616E686103073Q00506F6D70616E6F030A3Q0050752Q66657266697368030D3Q005361636162616D62617370697303083Q005361696C6669736803063Q0053616C6D6F6E030C3Q0053636F7270696F6E6669736803093Q0053656120486F727365030A3Q0053656120547572746C6503053Q00536861726B03053Q00537175696403073Q0053756E6669736803083Q0054616D626171756903043Q0054616E67030B3Q00546F7563616E204669736803053Q0054726F757403053Q005768616C65030D3Q0052657365742046696C7465727303063Q0042752Q746F6E03233Q005B4162792Q73616C5D20466973682066696C7465722073656374696F6E20612Q646564032C3Q004661726D2053652Q74696E6773205B44616E6765726F75732C204564697420776974682043617574696F6E5D032D3Q0074772Q656E4475726174696F6E202D205365636F6E647320746F20436F6D706C65746520416E696D6174696F6E030E3Q0054772Q656E204475726174696F6E026Q00E03F03013Q007303153Q00526573657420746F2044656661756C74202833732903313Q007265747265617453702Q65644D756C7469706C696572202D204D756C7469706C69657320526574726561742053702Q656403133Q00526574726561742053702Q6564204D756C746903013Q007803153Q00526573657420746F2044656661756C74202832782903203Q006D696E44697374202D20466973682053682Q6F74696E672044697374616E6365030C3Q004D696E2044697374616E6365026Q00444003063Q00207374756473031B3Q00526573657420746F2044656661756C74202832352073747564732903233Q0074772Q656E5374657073202D20506F736974696F6E2055706461746520416D6F756E74030B3Q0054772Q656E20537465707303153Q00526573657420746F2044656661756C74202833302903283Q005B4162792Q73616C5D20416476616E6365642073656374696F6E207769646765747320612Q64656403083Q0054656C65706F727403093Q004C6F636174696F6E7303263Q005B4162792Q73616C5D2054656C65706F7274207461622F73656374696F6E206372656174656403213Q005B4162792Q73616C5D20412Q6465642074656C65706F72742062752Q746F6E3A2003043Q004D69736303093Q005574696C697469657303213Q00546869732069732061206E6F636C697020616E7469636865617420627970612Q7303223Q00596F752077692Q6C206861766520746F2072656A6F696E20746F2064697361626C6503283Q005468657265666F726520796F752063612Q6E6F7420746F756368206C616E64206E6F722073652Q6C030E3Q00456E61626C65204E6F2D636C6970031A3Q005B4162792Q73616C5D204D69736320746162206372656174656403083Q0053652Q74696E6773030D3Q004D61696E2053652Q74696E6773030A3Q00546F2Q676C652047554903013Q004C031E3Q005B4162792Q73616C5D2053652Q74696E677320746162206372656174656403193Q005B4162792Q73616C5D2055492066752Q6C79206C6F61646564031E3Q005B4162792Q73616C5D20412Q6C2073797374656D73206C61756E6368656400FF022Q0012313Q00013Q00203F5Q0002001236000200034Q003E3Q0002000200203900013Q0004001231000200013Q00203F000200020002001236000400054Q003E000200040002001231000300063Q001236000400074Q000E0003000200012Q001200033Q0004001231000400093Q00203900040004000A0012360005000B3Q0012360006000C3Q0012360007000D4Q003E000400070002001014000300080004001231000400093Q00203900040004000A0012360005000F3Q001236000600103Q001236000700114Q003E0004000700020010140003000E0004001231000400093Q00203900040004000A001236000500133Q001236000600143Q001236000700154Q003E000400070002001014000300120004001231000400093Q00203900040004000A001236000500173Q001236000600183Q001236000700194Q003E000400070002001014000300160004001236000400084Q005E000500030004001231000600063Q0012360007001A4Q0043000800044Q00760007000700082Q000E0006000200012Q003B00065Q0012360007001B3Q0012360008001C3Q0012360009001D4Q003B000A6Q003B000B6Q0025000C000C4Q0012000D5Q001236000E001E3Q001236000F001F3Q001236001000203Q001236001100214Q006A0012000E00112Q001200136Q001200146Q001200156Q001200165Q001231001700063Q001236001800224Q000E001700020001001231001700063Q001236001800234Q0043001900084Q00760018001800192Q000E001700020001001231001700063Q001236001800244Q00430019000E4Q00760018001800192Q000E001700020001001231001700063Q001236001800254Q0043001900104Q00760018001800192Q000E0017000200012Q001200176Q001200186Q001200195Q000613001A3Q000100042Q00673Q00184Q00673Q00194Q00673Q00134Q00673Q00143Q000613001B0001000100052Q00673Q00134Q00673Q00144Q00673Q00174Q00673Q00184Q00673Q00193Q00024A001C00023Q000613001D0003000100012Q00673Q00013Q001231001E00063Q001236001F00264Q000E001E00020001000613001E0004000100082Q00673Q000B4Q00673Q00014Q00673Q00114Q00673Q00124Q00673Q001C4Q00673Q00064Q00673Q000D4Q00673Q001D3Q000613001F0005000100032Q00673Q00014Q00673Q001C4Q00673Q001D3Q001231002000063Q001236002100274Q000E002000020001001231002000063Q001236002100284Q000E002000020001001231002000293Q001231002100013Q00203F00210021002A0012360023002B6Q002100234Q005000203Q00022Q0052002000010001001231002000063Q0012360021002C3Q0012310022002D3Q0012310023002E4Q007B0022000200022Q00760021002100222Q000E0020000200010012310020002F3Q001236002100303Q001236002200313Q0012360023001D4Q00420020002300010012310020002E3Q00203F0020002000322Q001200223Q0003003080002200330034001231002300363Q00203900230023000A001236002400373Q001236002500384Q003E00230025000200101400220035002300308000220039003A2Q003E00200022000200203900210020003B00203900210021003C0012310022003E3Q00203900220022003F001236002300403Q001236002400413Q001236002500424Q003E0022002500020010140021003D002200203900210020003B00203900210021003C0012310022003E3Q00203900220022003F001236002300443Q001236002400453Q001236002500464Q003E00220025000200101400210043002200203900210020003B00203900210021003C0012310022003E3Q00203900220022003F001236002300213Q001236002400483Q001236002500494Q003E00220025000200101400210047002200203900210020003B00203900210021003C0012310022003E3Q00203900220022003F0012360023004B3Q0012360024004C3Q0012360025004D4Q003E0022002500020010140021004A002200203900210020003B00203900210021003C0012310022003E3Q00203900220022003F0012360023001D3Q0012360024004F3Q001236002500214Q003E0022002500020010140021004E002200203900210020003B00203900210021003C0012310022003E3Q00203900220022003F001236002300513Q001236002400523Q0012360025004C4Q003E00220025000200101400210050002200203900210020003B00203900210021003C0012310022003E3Q00203900220022003F001236002300463Q001236002400543Q001236002500424Q003E00220025000200101400210053002200203900210020003B00203900210021003C0012310022003E3Q00203900220022003F001236002300563Q001236002400413Q001236002500424Q003E00220025000200101400210055002200203900210020003B00203900210021003C00308000210057005100203900210020003B00203900210021003C003080002100580052001231002100063Q001236002200594Q000E002100020001001231002100063Q0012360022005A4Q000E00210002000100203F00210020005B2Q001200233Q000100308000230033005C2Q003E00210023000200203F00220021005D2Q001200243Q000100308000240033005E2Q003E00220024000200203F00230022005F2Q001200253Q00010030800025003300602Q004200230025000100203F00230022005F2Q001200253Q00010030800025003300612Q004200230025000100203F00230022005F2Q001200253Q00010030800025003300622Q004200230025000100203900230022006300308000230064003A00203F00230021005D2Q001200253Q00010030800025003300652Q003E00230025000200203900240023006300308000240064003A2Q001200243Q000300203F00250023005F2Q001200273Q00010030800027003300672Q003E00250027000200101400240066002500203F00250023005F2Q001200273Q00010030800027003300692Q003E00250027000200101400240068002500203F00250023005F2Q001200273Q000100308000270033006B2Q003E0025002700020010140024006A0025001231002500063Q0012360026006C4Q000E0025000200010012310025006D3Q00203900250025006E00061300260006000100022Q00673Q00204Q00673Q00244Q000E00250002000100203F00250020005B2Q001200273Q000100308000270033006F2Q003E00250027000200203F00260025005D2Q001200283Q00010030800028003300702Q003E002600280002001231002700063Q001236002800714Q000E00270002000100203F0027002600722Q001200293Q0002003080002900330073003080002900740075000613002A0007000100062Q00673Q00064Q00673Q00014Q00673Q001D4Q00673Q001C4Q00673Q000B4Q00673Q000C4Q00420027002A000100203F0027002600762Q001200293Q0002003080002900330077001231002A00793Q002039002A002A007A002039002A002A007B00101400290078002A000613002A0008000100062Q00673Q00064Q00673Q00014Q00673Q001D4Q00673Q001C4Q00673Q000B4Q00673Q000C3Q00024A002B00094Q00420027002B00012Q001200275Q0012310028007C4Q0043002900034Q000400280002002A00047A3Q00532Q01001231002D007D3Q002039002D002D007E2Q0043002E00274Q0043002F002B4Q0042002D002F00010006680028004E2Q01000200047A3Q004E2Q01001231002800063Q0012360029007F3Q001231002A007D3Q002039002A002A00802Q0043002B00273Q001236002C00814Q003E002A002C00022Q007600290029002A2Q000E00280002000100203F0028002600822Q0012002A3Q0003003080002A00330083001014002A00840027001014002A00740004000613002B000A000100032Q00673Q00044Q00673Q00054Q00673Q00034Q00420028002B000100203F0028002600852Q0012002A3Q0006003080002A00330086003080002A0087001D003080002A00880040003080002A00890051001014002A00740008003080002A008A008B000613002B000B000100012Q00673Q00084Q00420028002B000100203F0028002600852Q0012002A3Q0006003080002A0033008C003080002A0087001B003080002A0088004C003080002A0089008D003080002A0074001D003080002A008A008B000613002B000C000100012Q00673Q00094Q00420028002B0001001231002800063Q0012360029008E4Q000E0028000200012Q0012002800163Q0012360029008F3Q001236002A00903Q001236002B00913Q001236002C00923Q001236002D00933Q001236002E00943Q001236002F00953Q001236003000963Q001236003100973Q001236003200983Q001236003300993Q0012360034009A3Q0012360035009B3Q0012360036009C3Q0012360037009D3Q0012360038009E3Q0012360039009F3Q001236003A00A03Q001236003B00A13Q001236003C00A23Q001236003D00A33Q001236003E00A43Q001236003F00A53Q001236004000A63Q001236004100A73Q001236004200A83Q001236004300A93Q001236004400AA4Q00770028001C00012Q00250029002B3Q00203F002C0025005D2Q0012002E3Q0001003080002E003300AB2Q003E002C002E000200203F002D002C005F2Q0012002F3Q0001003080002F003300AC2Q0042002D002F000100203F002D002C00AD2Q0012002F3Q0003003080002F003300AE001014002F008400282Q001200305Q001014002F007400300006130030000D000100032Q00673Q00134Q00673Q001A4Q00673Q00174Q003E002D003000022Q00430029002D3Q00203F002D002C005F2Q0012002F3Q0001003080002F003300AF2Q0042002D002F000100203F002D002C00AD2Q0012002F3Q0003003080002F003300B02Q0012003000133Q001236003100B13Q001236003200B23Q001236003300B33Q001236003400B43Q001236003500B53Q001236003600B63Q001236003700B73Q001236003800B83Q001236003900B93Q001236003A00BA3Q001236003B00BB3Q001236003C00BC3Q001236003D00BD3Q001236003E00BE3Q001236003F00BF3Q001236004000C03Q001236004100C13Q001236004200C23Q001236004300C33Q001236004400C43Q001236004500C53Q001236004600C64Q0077003000160001001014002F008400302Q001200305Q001014002F007400300006130030000E000100052Q00673Q00154Q00673Q00164Q00673Q00144Q00673Q001A4Q00673Q00174Q003E002D003000022Q0043002A002D3Q00203F002D002C00AD2Q0012002F3Q0003003080002F003300C72Q0012003000133Q001236003100C83Q001236003200C93Q001236003300CA3Q001236003400CB3Q001236003500CC3Q001236003600CD3Q001236003700CE3Q001236003800CF3Q001236003900D03Q001236003A00D13Q001236003B00D23Q001236003C00D33Q001236003D00D43Q001236003E00D53Q001236003F00D63Q001236004000D73Q001236004100D83Q001236004200D93Q001236004300DA3Q001236004400DB3Q001236004500DC3Q001236004600DD4Q0077003000160001001014002F008400302Q001200305Q001014002F007400300006130030000F000100052Q00673Q00164Q00673Q00154Q00673Q00144Q00673Q001A4Q00673Q00174Q003E002D003000022Q0043002B002D3Q00203F002D002C005F2Q0012002F3Q0001003080002F003300DE2Q0042002D002F000100203F002D002C00DF2Q0012002F3Q0001003080002F003300DE00061300300010000100092Q00673Q00134Q00673Q00154Q00673Q00164Q00673Q00144Q00673Q00294Q00673Q002A4Q00673Q002B4Q00673Q001A4Q00673Q00174Q0042002D00300001001231002D00063Q001236002E00E04Q000E002D0002000100203F002D0025005D2Q0012002F3Q0001003080002F003300E12Q003E002D002F000200203F002E002D005F2Q001200303Q00010030800030003300E22Q0042002E0030000100203F002E002D00852Q001200303Q00060030800030003300E300308000300087008D00308000300088001D0030800030008900E400308000300074001E0030800030008A00E500061300310011000100032Q00673Q000E4Q00673Q00124Q00673Q00114Q003E002E0031000200203F002F002D00DF2Q001200313Q00010030800031003300E600061300320012000100012Q00673Q002E4Q0042002F0032000100203F002F002D005F2Q001200313Q00010030800031003300E72Q0042002F0031000100203F002F002D00852Q001200313Q00060030800031003300E800308000310087008D0030800031008800510030800031008900E400308000310074001F0030800031008A00E900061300320013000100012Q00673Q000F4Q003E002F0032000200203F0030002D00DF2Q001200323Q00010030800032003300EA00061300330014000100012Q00673Q002F4Q004200300033000100203F0030002D005F2Q001200323Q00010030800032003300EB2Q004200300032000100203F0030002D00852Q001200323Q00060030800032003300EC0030800032008700510030800032008800400030800032008900510030800032007400ED0030800032008A00EE00061300330015000100012Q00673Q00104Q003E00300033000200203F0031002D00DF2Q001200333Q00010030800033003300EF00061300340016000100012Q00673Q00304Q004200310034000100203F0031002D005F2Q001200333Q00010030800033003300F02Q004200310033000100203F0031002D00852Q001200333Q00050030800033003300F100308000330087001D00308000330088004000308000330089005100308000330074002100061300340017000100032Q00673Q00114Q00673Q00124Q00673Q000E4Q003E00310034000200203F0032002D00DF2Q001200343Q00010030800034003300F200061300350018000100012Q00673Q00314Q0042003200350001001231003200063Q001236003300F34Q000E00320002000100203F00320020005B2Q001200343Q00010030800034003300F42Q003E00320034000200203F00330032005D2Q001200353Q00010030800035003300F52Q003E003300350002001231003400063Q001236003500F64Q000E0034000200010012310034007C4Q0043003500034Q000400340002003600047A3Q0094020100203F0039003300DF2Q0012003B3Q0001001014003B00330037000613003C0019000100032Q00673Q00374Q00673Q001F4Q00673Q00384Q00420039003C0001001231003900063Q001236003A00F74Q0043003B00374Q0076003A003A003B2Q000E0039000200012Q001500375Q000668003400860201000200047A3Q0086020100203F00340020005B2Q001200363Q00010030800036003300F82Q003E00340036000200203F00350034005D2Q001200373Q00010030800037003300F92Q003E00350037000200203F00360035005F2Q001200383Q00010030800038003300FA2Q004200360038000100203F00360035005F2Q001200383Q00010030800038003300FB2Q004200360038000100203F00360035005F2Q001200383Q00010030800038003300FC2Q004200360038000100203F0036003500DF2Q001200383Q00010030800038003300FD0006130039001A000100012Q00673Q00014Q0042003600390001001231003600063Q001236003700FE4Q000E00360002000100203F00360020005B2Q001200383Q00010030800038003300FF2Q003E00360038000200203F00370036005D2Q001200393Q0001003080003900332Q0001003E00370039000200203F0038003700762Q0012003A3Q0002001236003B002Q012Q001014003A0033003B001231003B00793Q002039003B003B007A001236003C0002013Q005E003B003B003C001014003A0078003B000613003B001B000100012Q00673Q00203Q00024A003C001C4Q00420038003C0001001231003800063Q00123600390003013Q000E003800020001001231003800063Q00123600390004013Q000E0038000200010012310038006D3Q00203900380038006E0006130039001D000100092Q00673Q00064Q00673Q000A4Q00673Q00014Q00673Q000D4Q00673Q001B4Q00673Q00074Q00673Q00084Q00673Q00094Q00673Q000C4Q000E0038000200010012310038006D3Q00203900380038006E0006130039001E000100042Q00673Q00064Q00673Q000C4Q00673Q000A4Q00673Q00014Q000E0038000200010012310038006D3Q00203900380038006E0006130039001F000100022Q00673Q00064Q00673Q00014Q000E0038000200010012310038006D3Q00203900380038006E000613003900200001000E2Q00673Q00064Q00673Q000B4Q00673Q00014Q00673Q00074Q00673Q00084Q00673Q000A4Q00673Q000C4Q00673Q001E4Q00673Q00054Q00673Q00124Q00673Q000F4Q00673Q00174Q00673Q00094Q00673Q00104Q000E003800020001001231003800063Q00123600390005013Q000E0038000200012Q00453Q00013Q00213Q00023Q0003063Q006970616972732Q0100154Q00128Q00548Q00128Q00543Q00013Q0012313Q00014Q001A000100024Q00043Q0002000200047A3Q000A00012Q001A00055Q00201D0005000400020006683Q00080001000200047A3Q000800010012313Q00014Q001A000100034Q00043Q0002000200047A3Q001200012Q001A000500013Q00201D0005000400020006683Q00100001000200047A3Q001000012Q00453Q00017Q000D3Q00028Q00030E3Q0046696E6446697273744368696C6403043Q004865616403083Q00522Q6F7450617274010003053Q00737461747303043Q004669736803083Q004D75746174696F6E03053Q004C6162656C03083Q00666973685479706503043Q0054657874030C3Q00666973684D75746174696F6E3Q01634Q001A00016Q0016000100013Q000E4E000100050001000100047A3Q000500012Q001800016Q003B000100014Q001A000200014Q0016000200023Q000E4E0001000B0001000200047A3Q000B00012Q001800026Q003B000200013Q000673000100120001000100047A3Q00120001000673000200120001000100047A3Q001200012Q003B000300014Q0021000300024Q001A000300024Q005E000300033Q000673000300480001000100047A3Q0048000100203F00043Q0002001236000600034Q003E0004000600020006730004001E0001000100047A3Q001E000100203F00043Q0002001236000600044Q003E000400060002000673000400240001000100047A3Q002400012Q001A000500023Q00201D00053Q00052Q003B00056Q0021000500023Q00203F000500040002001236000700064Q003E0005000700020006730005002D0001000100047A3Q002D00012Q001A000600023Q00201D00063Q00052Q003B00066Q0021000600023Q00203F000600050002001236000800074Q003E00060008000200203F000700050002001236000900084Q003E000700090002000656000800380001000700047A3Q0038000100203F000800070002001236000A00094Q003E0008000A000200065F0006003C00013Q00047A3Q003C0001000673000800400001000100047A3Q004000012Q001A000900023Q00201D00093Q00052Q003B00096Q0021000900024Q001200093Q0002002039000A0006000B0010140009000A000A002039000A0008000B0010140009000C000A2Q0043000300094Q001A000900024Q001700093Q00030026700003004C0001000500047A3Q004C00012Q003B00046Q0021000400023Q00065F0001005400013Q00047A3Q005400012Q001A000400033Q00203900050003000C2Q005E00040004000500261B000400540001000D00047A3Q005400012Q001800046Q003B000400013Q00065F0002005D00013Q00047A3Q005D00012Q001A000500043Q00203900060003000A2Q005E00050005000600261B0005005D0001000D00047A3Q005D00012Q001800056Q003B000500013Q000656000600610001000400047A3Q006100012Q0043000600054Q0021000600024Q00453Q00017Q00073Q0003063Q00747970656F6603083Q00496E7374616E636503063Q00697061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103083Q004261736550617274030A3Q0043616E436F2Q6C696465021B3Q00065F3Q000700013Q00047A3Q00070001001231000200014Q004300036Q007B00020002000200261B000200080001000200047A3Q000800012Q00453Q00013Q001231000200033Q00203F00033Q00042Q0028000300044Q000300023Q000400047A3Q00180001001231000700014Q0043000800064Q007B000700020002002670000700180001000200047A3Q0018000100203F000700060005001236000900064Q003E00070009000200065F0007001800013Q00047A3Q001800010010140006000700010006680002000D0001000200047A3Q000D00012Q00453Q00017Q00073Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403163Q00412Q73656D626C794C696E65617256656C6F6369747903073Q00566563746F72332Q033Q006E6577028Q0001143Q0006460001000400013Q00047A3Q000400012Q001A00015Q002039000100010001000673000100070001000100047A3Q000700012Q00453Q00013Q00203F000200010002001236000400034Q003E00020004000200065F0002001300013Q00047A3Q00130001001231000300053Q002039000300030006001236000400073Q001236000500073Q001236000600074Q003E0003000600020010140002000400032Q00453Q00017Q00313Q0003063Q00506172656E7403043Q007761726E03343Q005B4162792Q73616C5D20736D2Q6F74684D6F7665546F3A20722Q6F74206973206E696C206F7220686173206E6F20706172656E7403093Q0043686172616374657203083Q00506F736974696F6E028Q0003053Q007072696E74032A3Q005B4162792Q73616C5D20736D2Q6F74684D6F7665546F2073746172746564202D3E207461726765743A2003083Q00746F737472696E67030A3Q00207C2073746570733A20026Q00F03F032B3Q005B4162792Q73616C5D20736D2Q6F74684D6F7665546F20696E74652Q727570746564206174207374657020033D3Q005B4162792Q73616C5D20736D2Q6F74684D6F7665546F3A2064657374506F73206F722063752Q72656E74506F73206973206E696C206174207374657020027Q004003063Q00747970656F6603073Q00566563746F723303093Q004D61676E6974756465026Q00244003063Q006E756D626572032B3Q005B4162792Q73616C5D20736D2Q6F74684D6F7665546F3A20737475636B20646574656374656420666F7220030E3Q00207C206D6F766564446973743A2003083Q00536166655A6F6E652Q0103173Q005B4162792Q73616C5D20426C61636B6C69737465643A2003063Q0020283135732903043Q007461736B03053Q0064656C6179026Q002E4003013Q005803013Q005903013Q005A03043Q006D61746803043Q007371727403333Q005B4162792Q73616C5D20736D2Q6F74684D6F7665546F3A2073746F7020636F6E646974696F6E206D657420617420646973742003053Q00666C2Q6F7203053Q0020666F72202Q033Q006E657703093Q00776F726B737061636503043Q0047616D6503053Q005475626573030E3Q0046696E6446697273744368696C6403043Q004E616D6503083Q00522Q6F7450617274025Q00804640026Q00144003053Q007063612Q6C030B3Q006D6F75736531636C69636B03043Q007761697403233Q005B4162792Q73616C5D20736D2Q6F74684D6F7665546F2066696E6973686564202D3E2006EF3Q00065F3Q000500013Q00047A3Q0005000100203900063Q00010006730006000B0001000100047A3Q000B0001001231000600023Q001236000700034Q000E0006000200012Q003B00066Q005400066Q00453Q00014Q001A000600013Q002039000600060004000646000700100001000300047A3Q001000012Q001A000700023Q000646000800130001000400047A3Q001300012Q001A000800033Q00203900093Q0005001236000A00063Q001231000B00073Q001236000C00083Q001231000D00094Q0043000E00054Q007B000D00020002001236000E000A4Q0043000F00074Q0076000C000C000F2Q000E000B000200012Q003B000B00014Q0054000B6Q001A000B00044Q0043000C00064Q003B000D6Q0042000B000D0001001236000B000B4Q0043000C00073Q001236000D000B3Q000461000B00DC00012Q001A000F00053Q00065F000F002E00013Q00047A3Q002E00012Q001A000F5Q000673000F00340001000100047A3Q00340001001231000F00073Q0012360010000C4Q00430011000E4Q00760010001000112Q000E000F0002000100047A3Q00DC00012Q0043000F00014Q0005000F0001000200203900103Q000500065F000F003B00013Q00047A3Q003B0001000673001000410001000100047A3Q00410001001231001100023Q0012360012000D4Q00430013000E4Q00760012001200132Q000E00110002000100047A3Q00DC00012Q0066000A000A0008000E74000E00790001000A00047A3Q00790001001236001100063Q0012310012000F4Q0043001300104Q007B001200020002002670001200520001001000047A3Q005200010012310012000F4Q0043001300094Q007B001200020002002670001200520001001000047A3Q005200012Q002F00120010000900203900110012001100047A3Q00530001001236001100123Q0012310012000F4Q0043001300114Q007B001200020002002670001200770001001300047A3Q00770001002624001100770001000B00047A3Q00770001001231001200023Q001236001300143Q001231001400094Q0043001500054Q007B001400020002001236001500154Q0043001600114Q00760013001300162Q000E00120002000100065F000500DC00013Q00047A3Q00DC000100261B000500DC0001001600047A3Q00DC00012Q001A001200063Q00201D001200050017001231001200073Q001236001300184Q0043001400053Q001236001500194Q00760013001300152Q000E0012000200010012310012001A3Q00203900120012001B0012360013001C3Q00061300143Q000100022Q00813Q00064Q00673Q00054Q004200120014000100047A3Q00DC00012Q0043000900103Q001236000A00063Q0020390011000F001D00203900120010001D2Q002F0011001100120020390012000F001E00203900130010001E2Q002F0012001200130020390013000F001F00203900140010001F2Q002F001300130014001231001400203Q0020390014001400212Q005A0015001100112Q005A0016001200122Q00660015001500162Q005A0016001300132Q00660015001500162Q007B00140002000200065F0002009E00013Q00047A3Q009E00012Q0043001500024Q0043001600144Q007B00150002000200065F0015009E00013Q00047A3Q009E0001001231001500073Q001236001600223Q001231001700203Q0020390017001700232Q0043001800144Q007B001700020002001236001800243Q001231001900094Q0043001A00054Q007B0019000200022Q00760016001600192Q000E00150002000100047A3Q00DC00012Q002F00150007000E00202D00150015000B0010110015000B0015001231001600103Q00203900160016002500203900170010001D0020390018000F001D00203900190010001D2Q002F0018001800192Q005A0018001800152Q006600170017001800203900180010001E0020390019000F001E002039001A0010001E2Q002F00190019001A2Q005A0019001900152Q006600180018001900203900190010001F002039001A000F001F002039001B0010001F2Q002F001A001A001B2Q005A001A001A00152Q006600190019001A2Q003E0016001900022Q001A001700074Q0043001800064Q000E0017000200010010143Q00050016001231001700263Q00203900170017002700203900170017002800203F0017001700292Q001A001900013Q00203900190019002A2Q003E00170019000200065F001700CA00013Q00047A3Q00CA000100203F001800170029001236001A002B4Q003E0018001A000200065F001800CA00013Q00047A3Q00CA000100203900180017002B001014001800050016001231001800203Q0020390018001800212Q005A0019001100112Q005A001A001300132Q006600190019001A2Q007B001800020002002624001400D70001002C00047A3Q00D70001000E23002D00D70001001800047A3Q00D700010012310019002E3Q001231001A002F4Q000E0019000200010012310019001A3Q0020390019001900302Q0043001A00084Q000E00190002000100041E000B00280001001231000B00073Q001236000C00313Q001231000D00094Q0043000E00054Q007B000D000200022Q0076000C000C000D2Q000E000B000200012Q001A000B00074Q001A000C00013Q002039000C000C00042Q000E000B000200012Q001A000B00044Q001A000C00013Q002039000C000C00042Q003B000D00014Q0042000B000D00012Q003B000B6Q0054000B6Q00453Q00013Q00013Q00034Q0003053Q007072696E7403193Q005B4162792Q73616C5D20556E626C61636B6C69737465643A2000094Q001A8Q001A000100013Q00201D3Q000100010012313Q00023Q001236000100034Q001A000200014Q00760001000100022Q000E3Q000200012Q00453Q00017Q001D3Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403043Q007761726E03303Q005B4162792Q73616C5D2074656C65706F7274546F3A2048756D616E6F6964522Q6F7450617274206E6F7420666F756E6403053Q007072696E74031A3Q005B4162792Q73616C5D2054656C65706F7274696E6720746F3A2003083Q00506F736974696F6E03013Q005803013Q005903013Q005A03043Q006D61746803043Q0073717274026Q0008402Q033Q006D6178026Q00244003053Q00666C2Q6F7202FCA9F1D24D62903F026Q00F03F03073Q00566563746F72332Q033Q006E657703093Q00776F726B737061636503043Q0047616D6503053Q00547562657303043Q004E616D6503083Q00522Q6F745061727403043Q007461736B03043Q0077616974031D3Q005B4162792Q73616C5D2054656C65706F727420636F6D706C6574653A2002804Q001A00025Q002039000200020001000656000300070001000200047A3Q0007000100203F000300020002001236000500034Q003E0003000500020006730003000D0001000100047A3Q000D0001001231000400043Q001236000500054Q000E0004000200012Q00453Q00013Q001231000400063Q001236000500074Q0043000600014Q00760005000500062Q000E0004000200012Q001A000400014Q0043000500024Q003B00066Q004200040006000100203900040003000800203900053Q00090020390006000400092Q002F00050005000600203900063Q000A00203900070004000A2Q002F00060006000700203900073Q000B00203900080004000B2Q002F0007000700080012310008000C3Q00203900080008000D2Q005A0009000500052Q005A000A000600062Q006600090009000A2Q005A000A000700072Q006600090009000A2Q007B0008000200020012360009000E3Q001231000A000C3Q002039000A000A000F001236000B00103Q001231000C000C3Q002039000C000C00112Q006A000D000800092Q0028000C000D4Q0050000A3Q0002001236000B00123Q001236000C00134Q0043000D000A3Q001236000E00133Q000461000C006500012Q006A0010000F000A001231001100143Q00203900110011001500203900120004000900203900133Q00090020390014000400092Q002F0013001300142Q005A0013001300102Q006600120012001300203900130004000A00203900143Q000A00203900150004000A2Q002F0014001400152Q005A0014001400102Q006600130013001400203900140004000B00203900153Q000B00203900160004000B2Q002F0015001500162Q005A0015001500102Q00660014001400152Q003E0011001400022Q001A001200024Q0043001300024Q000E001200020001001014000300080011001231001200163Q00203900120012001700203900120012001800203F0012001200022Q001A00145Q0020390014001400192Q003E00120014000200065F0012006000013Q00047A3Q0060000100203F0013001200020012360015001A4Q003E00130015000200065F0013006000013Q00047A3Q0060000100203900130012001A0010140013000800110012310013001B3Q00203900130013001C2Q00430014000B4Q000E00130002000100041E000C00360001001014000300083Q001231000C00163Q002039000C000C0017002039000C000C001800203F000C000C00022Q001A000E5Q002039000E000E00192Q003E000C000E000200065F000C007600013Q00047A3Q0076000100203F000D000C0002001236000F001A4Q003E000D000F000200065F000D007600013Q00047A3Q00760001002039000D000C001A001014000D00084Q001A000D00014Q0043000E00024Q003B000F00014Q0042000D000F0001001231000D00063Q001236000E001D4Q0043000F00014Q0076000E000E000F2Q000E000D000200012Q00453Q00017Q000F3Q0003053Q007072696E7403283Q005B4162792Q73616C5D20506572666F726D616E6365207374617473206C2Q6F70207374617274656403043Q0067616D65030A3Q004765745365727669636503053Q00537461747303103Q00506572666F726D616E6365537461747303053Q007061697273030B3Q004765744368696C6472656E03043Q004E616D6503083Q00496E7465726E616C03073Q0052752Q6E696E6703043Q007461736B03043Q0077616974026Q00F03F03053Q007063612Q6C00243Q0012313Q00013Q001236000100024Q000E3Q000200010012313Q00033Q00203F5Q0004001236000200054Q003E3Q000200020020395Q00062Q001200015Q001231000200073Q00203F00033Q00082Q0028000300044Q000300023Q000400047A3Q001000010020390007000600092Q00170001000700060006680002000E0001000200047A3Q000E000100061300023Q000100012Q00673Q00014Q001A00035Q00203900030003000A00203900030003000B00065F0003002300013Q00047A3Q002300010012310003000C3Q00203900030003000D0012360004000E4Q000E0003000200010012310003000F3Q00061300040001000100022Q00813Q00014Q00673Q00024Q000E00030002000100047A3Q001400012Q00453Q00013Q00023Q00073Q002Q033Q004E2F4103073Q00412Q6472652Q73030B3Q006D656D6F72795F7265616403063Q00737472696E67026Q006A40028Q00026Q006B40011A4Q001A00016Q005E000100013Q000673000100060001000100047A3Q00060001001236000200014Q0021000200023Q002039000200010002001231000300033Q001236000400043Q00202D0005000200052Q003E00030005000200065F0003001100013Q00047A3Q001100012Q0016000400033Q000E23000600110001000400047A3Q001100012Q0021000300023Q001231000400033Q001236000500043Q00202D0006000200072Q003E000400060002000646000500180001000400047A3Q00180001001236000500014Q0021000500024Q00453Q00017Q00073Q0003063Q004D656D6F72792Q033Q0053657403083Q004D656D6F72793A202Q033Q0043505503053Q004350553A202Q033Q0047505503053Q004750553A20001C4Q001A7Q0020395Q000100203F5Q0002001236000200034Q001A000300013Q001236000400014Q007B0003000200022Q00760002000200032Q00423Q000200012Q001A7Q0020395Q000400203F5Q0002001236000200054Q001A000300013Q001236000400044Q007B0003000200022Q00760002000200032Q00423Q000200012Q001A7Q0020395Q000600203F5Q0002001236000200074Q001A000300013Q001236000400064Q007B0003000200022Q00760002000200032Q00423Q000200012Q00453Q00017Q00073Q0003053Q007072696E74031D3Q005B4162792Q73616C5D204175746F206661726D20746F2Q676C65643A2003083Q00746F737472696E6703093Q00436861726163746572030A3Q006B657972656C65617365025Q0040524003283Q005B4162792Q73616C5D204175746F206661726D2073746F2Q7065642C20737461746520726573657401214Q00547Q001231000100013Q001236000200023Q001231000300034Q004300046Q007B0003000200022Q00760002000200032Q000E0001000200012Q001A00015Q000673000100200001000100047A3Q002000012Q001A000100013Q00203900010001000400065F0001002000013Q00047A3Q00200001001231000100053Q001236000200064Q000E0001000200012Q001A000100024Q00520001000100012Q001A000100034Q001A000200013Q0020390002000200042Q003B000300014Q00420001000300012Q003B00016Q0054000100044Q0025000100014Q0054000100053Q001231000100013Q001236000200074Q000E0001000200012Q00453Q00017Q00073Q0003053Q007072696E7403253Q005B4162792Q73616C5D204175746F206661726D206B657962696E6420746F2Q676C65643A2003083Q00746F737472696E6703093Q00436861726163746572030A3Q006B657972656C65617365025Q0040524003283Q005B4162792Q73616C5D204175746F206661726D2073746F2Q7065642C20737461746520726573657400234Q001A8Q001F8Q00547Q0012313Q00013Q001236000100023Q001231000200034Q001A00036Q007B0002000200022Q00760001000100022Q000E3Q000200012Q001A7Q0006733Q00220001000100047A3Q002200012Q001A3Q00013Q0020395Q000400065F3Q002200013Q00047A3Q002200010012313Q00053Q001236000100064Q000E3Q000200012Q001A3Q00024Q00523Q000100012Q001A3Q00034Q001A000100013Q0020390001000100042Q003B000200014Q00423Q000200012Q003B8Q00543Q00044Q00258Q00543Q00053Q0012313Q00013Q001236000100074Q000E3Q000200012Q00453Q00017Q00033Q0003053Q007072696E7403273Q005B4162792Q73616C5D204175746F6661726D206B657962696E64206368616E67656420746F3A2003083Q00746F737472696E6701083Q001231000100013Q001236000200023Q001231000300034Q004300046Q007B0003000200022Q00760002000200032Q000E0001000200012Q00453Q00017Q00043Q0003053Q007072696E7403203Q005B4162792Q73616C5D204661726D2061726561206368616E67656420746F3A2003083Q00207C20706F733A2003083Q00746F737472696E67010F4Q00548Q001A000100024Q001A00026Q005E0001000100022Q0054000100013Q001231000100013Q001236000200024Q001A00035Q001236000400033Q001231000500044Q001A000600014Q007B0005000200022Q00760002000200052Q000E0001000200012Q00453Q00017Q00033Q0003053Q007072696E7403233Q005B4162792Q73616C5D204F787967656E207468726573686F6C642073657420746F3A2003013Q002501084Q00547Q001231000100013Q001236000200024Q004300035Q001236000400034Q00760002000200042Q000E0001000200012Q00453Q00017Q00033Q0003053Q007072696E7403283Q005B4162792Q73616C5D204F787967656E207761726E696E672062752Q6665722073657420746F3A2003013Q002501084Q00547Q001231000100013Q001236000200024Q004300035Q001236000400034Q00760002000200042Q000E0001000200012Q00453Q00017Q00073Q00028Q0003053Q007072696E74033B3Q005B4162792Q73616C5D204D75746174696F6E2066696C74657220636C6561726564202D20746172676574696E6720612Q6C206D75746174696F6E73031F3Q005B4162792Q73616C5D204D75746174696F6E2066696C746572207365743A2003053Q007461626C6503063Q00636F6E63617403023Q002C2001164Q00548Q001A000100014Q00520001000100012Q001200016Q0054000100024Q001600015Q0026700001000C0001000100047A3Q000C0001001231000100023Q001236000200034Q000E00010002000100047A3Q00150001001231000100023Q001236000200043Q001231000300053Q0020390003000300062Q004300045Q001236000500074Q003E0003000500022Q00760002000200032Q000E0001000200012Q00453Q00017Q00093Q0003063Q0069706169727303053Q007461626C6503063Q00696E73657274028Q0003053Q007072696E7403383Q005B4162792Q73616C5D204669736820747970652066696C74657220636C6561726564202D20746172676574696E6720612Q6C20747970657303203Q005B4162792Q73616C5D204669736820747970652066696C746572207365743A2003063Q00636F6E63617403023Q002C20012E4Q00548Q001200015Q001231000200014Q001A00036Q000400020002000400047A3Q000B0001001231000700023Q0020390007000700032Q0043000800014Q0043000900064Q0042000700090001000668000200060001000200047A3Q00060001001231000200014Q001A000300014Q000400020002000400047A3Q00160001001231000700023Q0020390007000700032Q0043000800014Q0043000900064Q0042000700090001000668000200110001000200047A3Q001100012Q0054000100024Q001A000200034Q00520002000100012Q001200026Q0054000200044Q0016000200013Q002670000200240001000400047A3Q00240001001231000200053Q001236000300064Q000E00020002000100047A3Q002D0001001231000200053Q001236000300073Q001231000400023Q0020390004000400082Q0043000500013Q001236000600094Q003E0004000600022Q00760003000300042Q000E0002000200012Q00453Q00017Q00093Q0003063Q0069706169727303053Q007461626C6503063Q00696E73657274028Q0003053Q007072696E7403383Q005B4162792Q73616C5D204669736820747970652066696C74657220636C6561726564202D20746172676574696E6720612Q6C20747970657303203Q005B4162792Q73616C5D204669736820747970652066696C746572207365743A2003063Q00636F6E63617403023Q002C20012E4Q00548Q001200015Q001231000200014Q001A000300014Q000400020002000400047A3Q000B0001001231000700023Q0020390007000700032Q0043000800014Q0043000900064Q0042000700090001000668000200060001000200047A3Q00060001001231000200014Q001A00036Q000400020002000400047A3Q00160001001231000700023Q0020390007000700032Q0043000800014Q0043000900064Q0042000700090001000668000200110001000200047A3Q001100012Q0054000100024Q001A000200034Q00520002000100012Q001200026Q0054000200044Q0016000200013Q002670000200240001000400047A3Q00240001001231000200053Q001236000300064Q000E00020002000100047A3Q002D0001001231000200053Q001236000300073Q001231000400023Q0020390004000400082Q0043000500013Q001236000600094Q003E0004000600022Q00760003000300042Q000E0002000200012Q00453Q00017Q00033Q002Q033Q0053657403053Q007072696E7403203Q005B4162792Q73616C5D20412Q6C20666973682066696C7465727320726573657400254Q00128Q00548Q00128Q00543Q00014Q00128Q00543Q00024Q00128Q00543Q00034Q001A3Q00043Q00065F3Q000F00013Q00047A3Q000F00012Q001A3Q00043Q00203F5Q00012Q001200026Q00423Q000200012Q001A3Q00053Q00065F3Q001600013Q00047A3Q001600012Q001A3Q00053Q00203F5Q00012Q001200026Q00423Q000200012Q001A3Q00063Q00065F3Q001D00013Q00047A3Q001D00012Q001A3Q00063Q00203F5Q00012Q001200026Q00423Q000200012Q001A3Q00074Q00523Q000100012Q00128Q00543Q00083Q0012313Q00023Q001236000100034Q000E3Q000200012Q00453Q00017Q00023Q0003053Q007072696E7403203Q005B4162792Q73616C5D2074772Q656E4475726174696F6E2073657420746F3A20010B4Q00548Q001A00016Q001A000200024Q006A0001000100022Q0054000100013Q001231000100013Q001236000200024Q004300036Q00760002000200032Q000E0001000200012Q00453Q00017Q00043Q002Q033Q00536574026Q00084003053Q007072696E74032B3Q005B4162792Q73616C5D2074772Q656E4475726174696F6E20726573657420746F2064656661756C743A203300084Q001A7Q00203F5Q0001001236000200024Q00423Q000200010012313Q00033Q001236000100044Q000E3Q000200012Q00453Q00017Q00023Q0003053Q007072696E7403293Q005B4162792Q73616C5D207265747265617453702Q65644D756C7469706C6965722073657420746F3A2001074Q00547Q001231000100013Q001236000200024Q004300036Q00760002000200032Q000E0001000200012Q00453Q00017Q00043Q002Q033Q00536574027Q004003053Q007072696E7403343Q005B4162792Q73616C5D207265747265617453702Q65644D756C7469706C69657220726573657420746F2064656661756C743A203200084Q001A7Q00203F5Q0001001236000200024Q00423Q000200010012313Q00033Q001236000100044Q000E3Q000200012Q00453Q00017Q00023Q0003053Q007072696E74031A3Q005B4162792Q73616C5D206D696E446973742073657420746F3A2001074Q00547Q001231000100013Q001236000200024Q004300036Q00760002000200032Q000E0001000200012Q00453Q00017Q00043Q002Q033Q00536574026Q00444003053Q007072696E7403263Q005B4162792Q73616C5D206D696E4469737420726573657420746F2064656661756C743A20323500084Q001A7Q00203F5Q0001001236000200024Q00423Q000200010012313Q00033Q001236000100044Q000E3Q000200012Q00453Q00017Q00023Q0003053Q007072696E74031D3Q005B4162792Q73616C5D2074772Q656E53746570732073657420746F3A20010B4Q00548Q001A000100024Q001A00026Q006A0001000100022Q0054000100013Q001231000100013Q001236000200024Q004300036Q00760002000200032Q000E0001000200012Q00453Q00017Q00043Q002Q033Q00536574026Q003E4003053Q007072696E7403293Q005B4162792Q73616C5D2074772Q656E537465707320726573657420746F2064656661756C743A20333000084Q001A7Q00203F5Q0001001236000200024Q00423Q000200010012313Q00033Q001236000100044Q000E3Q000200012Q00453Q00017Q00043Q0003053Q007072696E7403233Q005B4162792Q73616C5D2054656C65706F72742062752Q746F6E207072652Q7365643A2003043Q007461736B03053Q00737061776E000D3Q0012313Q00013Q001236000100024Q001A00026Q00760001000100022Q000E3Q000200010012313Q00033Q0020395Q000400061300013Q000100032Q00813Q00014Q00813Q00024Q00818Q000E3Q000200012Q00453Q00013Q00018Q00054Q001A8Q001A000100014Q001A000200024Q00423Q000200012Q00453Q00017Q00043Q0003053Q007072696E74031B3Q005B4162792Q73616C5D204E6F2D636C69702061637469766174656403043Q007461736B03053Q00737061776E00093Q0012313Q00013Q001236000100024Q000E3Q000200010012313Q00033Q0020395Q000400061300013Q000100012Q00818Q000E3Q000200012Q00453Q00013Q00013Q001B3Q0003093Q00776F726B7370616365030E3Q0046696E6446697273744368696C642Q033Q004D617003063Q00646562726973030E3Q0047657444657363656E64616E7473026Q00F03F2Q033Q0049734103083Q004261736550617274030A3Q0043616E436F2Q6C696465010003053Q007063612Q6C03063Q00506172656E74025Q00408F40028Q0003043Q007461736B03043Q007761697403043Q007761726E03203Q005B4162792Q73616C5D204E6F2D636C69703A204D6170206E6F7420666F756E6403093Q0043686172616374657203063Q0069706169727303053Q007072696E7403233Q005B4162792Q73616C5D204E6F2D636C69703A2048756D616E6F6964522Q6F745061727403043Q0047616D6503053Q00547562657303043Q004E616D6503173Q005B4162792Q73616C5D204E6F2D636C69703A205475626503193Q005B4162792Q73616C5D204E6F2D636C69703A204C6F61646564005D3Q0012313Q00013Q00203F5Q0002001236000200034Q003E3Q00020002001231000100013Q00203F000100010002001236000300044Q003E00010003000200065F3Q002700013Q00047A3Q0027000100065F0001002700013Q00047A3Q0027000100203F00023Q00052Q007B000200020002001236000300064Q0016000400023Q001236000500063Q0004610003002600012Q005E00070002000600203F000800070007001236000A00084Q003E0008000A000200065F0008001E00013Q00047A3Q001E000100308000070009000A0012310008000B3Q00061300093Q000100012Q00673Q00074Q000E0008000200010010140007000C000100207E00080006000D002670000800240001000E00047A3Q002400010012310008000F3Q0020390008000800102Q00520008000100012Q001500075Q00041E00030012000100047A3Q002A0001001231000200113Q001236000300124Q000E0002000200012Q001A00025Q00203900020002001300065F0002004000013Q00047A3Q00400001001231000200144Q001A00035Q00203900030003001300203F0003000300052Q0028000300044Q000300023Q000400047A3Q003B000100203F000700060007001236000900084Q003E00070009000200065F0007003B00013Q00047A3Q003B000100308000060009000A000668000200350001000200047A3Q00350001001231000200153Q001236000300164Q000E000200020001001231000200013Q00203900020002001700203900020002001800203F0002000200022Q001A00045Q0020390004000400192Q003E00020004000200065F0002005900013Q00047A3Q00590001001231000300143Q00203F0004000200052Q0028000400054Q000300033Q000500047A3Q0054000100203F000800070007001236000A00084Q003E0008000A000200065F0008005400013Q00047A3Q0054000100308000070009000A0006680003004E0001000200047A3Q004E0001001231000300153Q0012360004001A4Q000E000300020001001231000300153Q0012360004001B4Q000E0003000200012Q00453Q00013Q00013Q00033Q0003083Q0043616E5175657279010003083Q0043616E546F75636800054Q001A7Q0030803Q000100022Q001A7Q0030803Q000300022Q00453Q00017Q00033Q0003063Q00546F2Q676C6503053Q007072696E7403153Q005B4162792Q73616C5D2047554920746F2Q676C656400074Q001A7Q00203F5Q00012Q000E3Q000200010012313Q00023Q001236000100034Q000E3Q000200012Q00453Q00017Q00033Q0003053Q007072696E7403223Q005B4162792Q73616C5D20475549206B657962696E64206368616E67656420746F3A2003083Q00746F737472696E6701083Q001231000100013Q001236000200023Q001231000300034Q004300046Q007B0003000200022Q00760002000200032Q000E0001000200012Q00453Q00017Q00223Q0003053Q007072696E7403203Q005B4162792Q73616C5D2046697368207363616E206C2Q6F70207374617274656403043Q007461736B03043Q0077616974026Q00E03F03093Q00776F726B737061636503043Q0047616D6503043Q0046697368030E3Q0046696E6446697273744368696C6403063Q00636C69656E7403093Q0043686172616374657203103Q0048756D616E6F6964522Q6F745061727403083Q00506F736974696F6E024Q007E842E41028Q0003063Q00697061697273030B3Q004765744368696C6472656E026Q00F03F03043Q004E616D6503043Q004865616403083Q00522Q6F7450617274030B3Q005072696D6172795061727403013Q005803013Q005903013Q005A03043Q006D61746803043Q0073717274026Q003E4003053Q007063612Q6C03103Q005B4162792Q73616C5D205363616E3A2003093Q0020746F74616C207C20030F3Q0020626C61636B6C6973746564207C2003143Q002066696C7465726564207C207461726765743A2003043Q006E6F6E6500953Q0012313Q00013Q001236000100024Q000E3Q000200010012313Q00033Q0020395Q0004001236000100054Q000E3Q000200012Q001A7Q00065F3Q000300013Q00047A3Q000300012Q001A3Q00013Q00065F3Q000E00013Q00047A3Q000E000100047A3Q000300010012313Q00063Q0020395Q00070020395Q000800065F3Q001900013Q00047A3Q001900010012313Q00063Q0020395Q00070020395Q000800203F5Q00090012360002000A4Q003E3Q000200020006733Q001C0001000100047A3Q001C000100047A3Q000300012Q001A000100023Q00203900010001000B000656000200230001000100047A3Q0023000100203F0002000100090012360004000C4Q003E000200040002000673000200260001000100047A3Q0026000100047A3Q0003000100203900030002000D2Q0025000400043Q0012360005000E3Q0012360006000F3Q0012360007000F3Q0012360008000F3Q001231000900103Q00203F000A3Q00112Q0028000A000B4Q000300093Q000B00047A3Q006E000100202D0006000600122Q001A000E00033Q002039000F000D00132Q005E000E000E000F00065F000E003900013Q00047A3Q0039000100202D00070007001200047A3Q006800012Q001A000E00044Q0043000F000D4Q007B000E0002000200065F000E006700013Q00047A3Q0067000100203F000E000D0009001236001000144Q003E000E00100002000673000E00490001000100047A3Q0049000100203F000E000D0009001236001000154Q003E000E00100002000673000E00490001000100047A3Q00490001002039000E000D001600065F000E006800013Q00047A3Q00680001002039000F000E000D00065F000F006800013Q00047A3Q00680001002039000F000E000D002039000F000F00170020390010000300172Q002F000F000F00100020390010000E000D0020390010001000180020390011000300182Q002F0010001000110020390011000E000D0020390011001100190020390012000300192Q002F0011001100120012310012001A3Q00203900120012001B2Q005A0013000F000F2Q005A0014001000102Q00660013001300142Q005A0014001100112Q00660013001300142Q007B00120002000200060A001200680001000500047A3Q006800012Q0043000500124Q00430004000D3Q00047A3Q0068000100202D00080008001200207E000E0006001C002670000E006E0001000F00047A3Q006E0001001231000E00033Q002039000E000E00042Q0052000E00010001000668000900310001000200047A3Q003100012Q003B00095Q001231000A001D3Q000613000B3Q000100052Q00813Q00024Q00813Q00054Q00673Q00094Q00813Q00064Q00813Q00074Q000E000A000200010006730009007D0001000100047A3Q007D00012Q0054000400083Q00047A3Q007F00012Q0025000A000A4Q0054000A00083Q001231000A00013Q001236000B001E4Q0043000C00063Q001236000D001F4Q0043000E00073Q001236000F00204Q0043001000083Q001236001100213Q00065F0004008C00013Q00047A3Q008C00010020390012000400130006730012008D0001000100047A3Q008D0001001236001200224Q0076000B000B00122Q000E000A000200012Q00157Q00047A3Q000300012Q00157Q00047A3Q0003000100047A3Q000300012Q00453Q00013Q00013Q00093Q0003093Q00506C6179657247756903043Q004D61696E030E3Q0046696E6446697273744368696C6403063Q004F787967656E03083Q00746F6E756D626572030C3Q00476574412Q7472696275746503093Q006F6C646F787967656E026Q005940029Q00224Q001A7Q0020395Q00010020395Q000200203F5Q0003001236000200044Q003E3Q0002000200065F3Q002100013Q00047A3Q00210001001231000100053Q00203F00023Q0006001236000400076Q000200044Q005000013Q0002000673000100100001000100047A3Q00100001001236000100084Q001A000200013Q000E23000900160001000200047A3Q001600012Q001A000200013Q000673000200170001000100047A3Q00170001001236000200084Q006A0003000100020020510003000300082Q001A000400034Q001A000500044Q006600040004000500067F000300020001000400047A3Q001F00012Q001800046Q003B000400014Q0054000400024Q00453Q00017Q00073Q0003053Q007072696E74031D3Q005B4162792Q73616C5D2043616D657261206C2Q6F702073746172746564028Q0003043Q007461736B03043Q0077616974029A5Q99A93F03053Q007063612Q6C00243Q0012313Q00013Q001236000100024Q000E3Q000200010012363Q00033Q001231000100043Q002039000100010005001236000200064Q000E0001000200012Q001A00015Q00065F0001001400013Q00047A3Q001400012Q001A000100013Q00065F0001001400013Q00047A3Q001400010012363Q00033Q001231000100073Q00061300023Q000100012Q00813Q00014Q000E00010002000100047A3Q000400012Q001A00015Q00065F0001000400013Q00047A3Q000400012Q001A000100013Q000673000100040001000100047A3Q000400012Q001A000100023Q000673000100040001000100047A3Q00040001001231000100073Q00061300020001000100022Q00813Q00034Q00678Q000E00010002000100047A3Q000400012Q00453Q00013Q00023Q00083Q00030E3Q0046696E6446697273744368696C6403043Q004865616403083Q00522Q6F7450617274030B3Q005072696D6172795061727403093Q00776F726B7370616365030D3Q0043752Q72656E7443616D65726103063Q006C2Q6F6B417403083Q00506F736974696F6E00194Q001A7Q00203F5Q0001001236000200024Q003E3Q000200020006733Q000E0001000100047A3Q000E00012Q001A7Q00203F5Q0001001236000200034Q003E3Q000200020006733Q000E0001000100047A3Q000E00012Q001A7Q0020395Q000400065F3Q001800013Q00047A3Q00180001001231000100053Q002039000100010006002039000100010007001231000200053Q00203900020002000600203900020002000800203900033Q00082Q00420001000300012Q00453Q00017Q00113Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F7450617274026Q00F03F025Q0080764003043Q006D6174682Q033Q00726164026Q00344003083Q00506F736974696F6E03073Q00566563746F72332Q033Q006E65772Q033Q00636F73028Q002Q033Q0073696E03093Q00776F726B7370616365030D3Q0043752Q72656E7443616D65726103063Q006C2Q6F6B4174002C4Q001A7Q0020395Q00010006560001000700013Q00047A3Q0007000100203F00013Q0002001236000300034Q003E0001000300020006730001000A0001000100047A3Q000A00012Q00453Q00014Q001A000200013Q00202D00020002000400207E0002000200052Q0054000200013Q001231000200063Q0020390002000200072Q001A000300014Q007B000200020002001236000300083Q0020390004000100090012310005000A3Q00203900050005000B001231000600063Q00203900060006000C2Q0043000700024Q007B0006000200022Q005A0006000600030012360007000D3Q001231000800063Q00203900080008000E2Q0043000900024Q007B0008000200022Q005A0008000800032Q003E0005000800022Q00660004000400050012310005000F3Q0020390005000500100020390005000500110012310006000F3Q0020390006000600100020390006000600092Q0043000700044Q00420005000700012Q00453Q00017Q00093Q0003053Q007072696E7403213Q005B4162792Q73616C5D204175746F2D6361746368206C2Q6F70207374617274656403043Q007461736B03043Q0077616974026Q00F03F03053Q007063612Q6C03043Q007761726E031C3Q005B4162792Q73616C5D204175746F2D636174636820652Q726F723A2003083Q00746F737472696E6700193Q0012313Q00013Q001236000100024Q000E3Q000200010012313Q00033Q0020395Q0004001236000100054Q000E3Q000200012Q001A7Q00065F3Q000300013Q00047A3Q000300010012313Q00063Q00061300013Q000100012Q00813Q00014Q00043Q000200010006733Q00030001000100047A3Q00030001001231000200073Q001236000300083Q001231000400094Q0043000500014Q007B0004000200022Q00760003000300042Q000E00020002000100047A3Q000300012Q00453Q00013Q00013Q00133Q0003093Q00506C6179657247756903043Q004D61696E030B3Q004361746368696E6742617203053Q004672616D652Q033Q0042617203053Q00436174636803053Q0047722Q656E03073Q00412Q6472652Q73030C3Q006D656D6F72795F777269746503053Q00666C6F6174025Q00A09440026Q00F03F025Q00B09440025Q00C09440025Q00D0944003053Q007072696E74032D3Q005B4162792Q73616C5D204175746F2D63617463683A206D656D6F7279207772692Q74656E20617420626173652003043Q007761726E03283Q005B4162792Q73616C5D204175746F2D63617463683A20636F6E74726F6C42617365206973206E696C00294Q001A7Q0020395Q00010020395Q00020020395Q00030020395Q00040020395Q000500203900013Q000600203900010001000700203900010001000800065F0001002500013Q00047A3Q00250001001231000200093Q0012360003000A3Q00202D00040001000B0012360005000C4Q0042000200050001001231000200093Q0012360003000A3Q00202D00040001000D0012360005000C4Q0042000200050001001231000200093Q0012360003000A3Q00202D00040001000E0012360005000C4Q0042000200050001001231000200093Q0012360003000A3Q00202D00040001000F0012360005000C4Q0042000200050001001231000200103Q001236000300114Q0043000400014Q00760003000300042Q000E00020002000100047A3Q00280001001231000200123Q001236000300134Q000E0002000200012Q00453Q00017Q00413Q0003053Q007072696E74031C3Q005B4162792Q73616C5D204D61696E206379636C652073746172746564028Q0003043Q007461736B03043Q0077616974029A5Q99B93F03083Q006B65797072652Q73025Q0040524003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403043Q007761726E03303Q005B4162792Q73616C5D204D61696E206379636C653A2048756D616E6F6964522Q6F7450617274206E6F7420666F756E6403093Q00506C6179657247756903043Q004D61696E03063Q004F787967656E03293Q005B4162792Q73616C5D204D61696E206379636C653A204F787967656E205549206E6F7420666F756E6403083Q00746F6E756D626572030C3Q00476574412Q7472696275746503093Q006F6C646F787967656E026Q00594003163Q005B4162792Q73616C5D204E6577206D61784F78793A20027Q0040030F3Q005B4162792Q73616C5D204F78793A2003043Q006D61746803053Q00666C2Q6F7203013Q002F03023Q00202803103Q002529207C207468726573686F6C643A2003103Q0025207C2072657472656174696E673A2003083Q00746F737472696E6703353Q005B4162792Q73616C5D204C4F57204F585947454E2C2052657472656174696E6720746F2073616665207A6F6E65207C206F78793A2003013Q0025025Q00805840031B3Q005B4162792Q73616C5D204F787967656E20726573746F726564202803113Q0025292C20726573756D696E67206661726D03053Q00737061776E03093Q00776F726B737061636503043Q0047616D6503043Q004669736803063Q00636C69656E74033D3Q005B4162792Q73616C5D204669736820666F6C646572206E6F7420666F756E6420617420776F726B73706163652E47616D652E466973682E636C69656E7403063Q00506172656E7403043Q004E616D65010003083Q00666973685479706503013Q003F030C3Q00666973684D75746174696F6E03163Q005B4162792Q73616C5D204E6577207461726765743A2003013Q002903083Q00522Q6F745061727403043Q004865616403083Q00506F736974696F6E03013Q005803013Q005903013Q005A03043Q0073717274031A3Q005B4162792Q73616C5D204D6F76696E6720746F20666973683A2003093Q00207C20646973743A20026Q00144003233Q005B4162792Q73616C5D20496E2072616E67652C20636C69636B696E6720666973683A2003053Q007063612Q6C030B3Q006D6F75736531636C69636B00033F3Q005B4162792Q73616C5D204E6F2076616C696420746172676574206669736820666F756E64202866696C746572206D617920626520742Q6F20737472696374290025012Q0012313Q00013Q001236000100024Q000E3Q000200012Q00257Q001236000100033Q001231000200043Q002039000200020005001236000300064Q000E0002000200012Q001A00025Q00065F0002000500013Q00047A3Q000500012Q001A000200013Q00065F0002001000013Q00047A3Q0010000100047A3Q00050001001231000200073Q001236000300084Q000E0002000200012Q001A000200023Q0020390002000200090006560003001A0001000200047A3Q001A000100203F00030002000A0012360005000B4Q003E000300050002000673000300200001000100047A3Q002000010012310004000C3Q0012360005000D4Q000E00040002000100047A3Q000500012Q001A000400023Q00203900040004000E00203900040004000F00203F00040004000A001236000600104Q003E0004000600020006730004002B0001000100047A3Q002B00010012310005000C3Q001236000600114Q000E00050002000100065F0004003400013Q00047A3Q00340001001231000500123Q00203F000600040013001236000800146Q000600084Q005000053Q0002000673000500350001000100047A3Q00350001001236000500154Q001A000600033Q00060A0006003E0001000500047A3Q003E00012Q0054000500033Q001231000600013Q001236000700164Q001A000800034Q00760007000700082Q000E0006000200012Q001A000600033Q000E23000300440001000600047A3Q004400012Q001A000600033Q000673000600450001000100047A3Q00450001001236000600154Q006A00070005000600205100070007001500202D000100010006000E74001700600001000100047A3Q00600001001231000800013Q001236000900183Q001231000A00193Q002039000A000A001A2Q0043000B00054Q007B000A00020002001236000B001B4Q0043000C00063Q001236000D001C3Q001231000E00193Q002039000E000E001A2Q0043000F00074Q007B000E00020002001236000F001D4Q001A001000043Q0012360011001E3Q0012310012001F4Q001A001300054Q007B0012000200022Q00760009000900122Q000E000800020001001236000100033Q00065F0004007400013Q00047A3Q007400012Q001A000800043Q000632000700740001000800047A3Q007400012Q001A000800053Q000673000800740001000100047A3Q007400012Q003B000800014Q0054000800053Q001231000800013Q001236000900203Q001231000A00193Q002039000A000A001A2Q0043000B00074Q007B000A00020002001236000B00214Q007600090009000B2Q000E00080002000100047A3Q00840001000E74002200840001000700047A3Q008400012Q001A000800053Q00065F0008008400013Q00047A3Q008400012Q003B00086Q0054000800053Q001231000800013Q001236000900233Q001231000A00193Q002039000A000A001A2Q0043000B00074Q007B000A00020002001236000B00244Q007600090009000B2Q000E0008000200012Q001A000800053Q00065F0008009400013Q00047A3Q009400012Q0025000800084Q0054000800063Q001231000800043Q00203900080008002500061300093Q000100052Q00813Q00074Q00673Q00034Q00813Q00084Q00813Q00094Q00813Q000A4Q000E0008000200012Q001500025Q00047A3Q00050001001231000800263Q0020390008000800270020390008000800280020390008000800290006730008009F0001000100047A3Q009F00010012310009000C3Q001236000A002A4Q000E0009000200012Q001500025Q00047A3Q000500012Q001A000900063Q00065F000900192Q013Q00047A3Q00192Q01002039000A0009002B00065F000A00192Q013Q00047A3Q00192Q01002039000A0009002C0006553Q00C30001000A00047A3Q00C300012Q001A000A000B4Q005E000A000A000900065F000A00B100013Q00047A3Q00B1000100261B000A00B10001002D00047A3Q00B10001002039000B000A002E000673000B00B20001000100047A3Q00B20001001236000B002F3Q00065F000A00B900013Q00047A3Q00B9000100261B000A00B90001002D00047A3Q00B90001002039000C000A0030000673000C00BA0001000100047A3Q00BA0001001236000C002F3Q001231000D00013Q001236000E00314Q0043000F000B3Q0012360010001C4Q00430011000C3Q001236001200324Q0076000E000E00122Q000E000D000200010020393Q0009002C00203F000A0009000A001236000C000B4Q003E000A000C0002000673000A00D00001000100047A3Q00D0000100203F000A0009000A001236000C00334Q003E000A000C0002000673000A00D00001000100047A3Q00D0000100203F000A0009000A001236000C00344Q003E000A000C000200065F000A001F2Q013Q00047A3Q001F2Q01002039000B000A0035002039000C000B0036002039000D00030035002039000D000D00362Q002F000C000C000D002039000D000B0037002039000E00030035002039000E000E00372Q002F000D000D000E002039000E000B0038002039000F00030035002039000F000F00382Q002F000E000E000F001231000F00193Q002039000F000F00392Q005A0010000C000C2Q005A0011000D000D2Q00660010001000112Q005A0011000E000E2Q00660010001000112Q007B000F000200022Q001A001000044Q001A0011000C4Q006600100010001100067F000700020001001000047A3Q00ED00012Q001800106Q003B001000014Q001A0011000D3Q00060A001100062Q01000F00047A3Q00062Q01000673001000062Q01000100047A3Q00062Q01001231001100013Q0012360012003A3Q00203900130009002C0012360014003B3Q001231001500193Q00203900150015001A2Q00430016000F4Q007B0015000200022Q00760012001200152Q000E001100020001001231001100043Q00203900110011002500061300120001000100042Q00813Q00074Q00673Q00034Q00673Q00094Q00813Q000D4Q000E00110002000100047A3Q001F2Q010006730010001F2Q01000100047A3Q001F2Q01001231001100193Q0020390011001100392Q005A0012000C000C2Q005A0013000E000E2Q00660012001200132Q007B001100020002000E23003C001F2Q01001100047A3Q001F2Q01001231001100013Q0012360012003D3Q00203900130009002C2Q00760012001200132Q000E0011000200010012310011003E3Q0012310012003F4Q000E00110002000100047A3Q001F2Q0100261B3Q001F2Q01004000047A3Q001F2Q01001231000A00013Q001236000B00414Q000E000A000200012Q00258Q001500025Q00047A3Q000500012Q001500025Q00047A3Q0005000100047A3Q000500012Q00453Q00013Q00023Q00023Q00026Q004E4003083Q00536166655A6F6E65000C4Q001A8Q001A000100013Q00061300023Q000100012Q00813Q00024Q0025000300033Q001236000400014Q001A000500034Q001A000600044Q006A000500050006001236000600024Q00423Q000600012Q00453Q00013Q00018Q00034Q001A8Q00213Q00024Q00453Q00017Q00013Q0003043Q004E616D65000D4Q001A8Q001A000100013Q00061300023Q000100012Q00813Q00023Q00061300030001000100032Q00813Q00024Q00813Q00034Q00813Q00014Q0025000400054Q001A000600023Q0020390006000600012Q00423Q000600012Q00453Q00013Q00023Q000C3Q0003063Q00506172656E74030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403083Q00522Q6F745061727403043Q004865616403073Q00566563746F72332Q033Q006E657703083Q00506F736974696F6E03013Q0058026Q00244003013Q005903013Q005A00274Q001A7Q00065F3Q002400013Q00047A3Q002400012Q001A7Q0020395Q000100065F3Q002400013Q00047A3Q002400012Q001A7Q00203F5Q0002001236000200034Q003E3Q000200020006733Q00170001000100047A3Q001700012Q001A7Q00203F5Q0002001236000200044Q003E3Q000200020006733Q00170001000100047A3Q001700012Q001A7Q00203F5Q0002001236000200054Q003E3Q0002000200065F3Q002400013Q00047A3Q00240001001231000100063Q00203900010001000700203900023Q000800203900020002000900202D00020002000A00203900033Q000800203900030003000B00203900043Q000800203900040004000C2Q0006000100044Q004C00016Q00258Q00213Q00024Q00453Q00017Q00093Q00030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403083Q00522Q6F745061727403043Q004865616403043Q006D6174682Q033Q0061627303083Q00506F736974696F6E03013Q0059026Q002040012D4Q001A00015Q00065F0001001300013Q00047A3Q001300012Q001A00015Q00203F000100010001001236000300024Q003E000100030002000673000100130001000100047A3Q001300012Q001A00015Q00203F000100010001001236000300034Q003E000100030002000673000100130001000100047A3Q001300012Q001A00015Q00203F000100010001001236000300044Q003E00010003000200065F0001002600013Q00047A3Q002600012Q001A000200013Q0006323Q00230001000200047A3Q00230001001231000200053Q0020390002000200062Q001A000300023Q0020390003000300070020390003000300080020390004000100070020390004000400082Q002F0003000300042Q007B000200020002002648000200240001000900047A3Q002400012Q001800026Q003B000200014Q0021000200024Q001A000200013Q00067F3Q00020001000200047A3Q002A00012Q001800026Q003B000200014Q0021000200024Q00453Q00017Q00", GetFEnv(), ...);