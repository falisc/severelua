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
				if (Enum <= 42) then
					if (Enum <= 20) then
						if (Enum <= 9) then
							if (Enum <= 4) then
								if (Enum <= 1) then
									if (Enum == 0) then
										if (Stk[Inst[2]] < Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum <= 2) then
									local A = Inst[2];
									local B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								elseif (Enum > 3) then
									if (Stk[Inst[2]] == Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 6) then
								if (Enum > 5) then
									local A = Inst[2];
									local B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								else
									local A = Inst[2];
									Stk[A](Stk[A + 1]);
								end
							elseif (Enum <= 7) then
								Stk[Inst[2]] = Env[Inst[3]];
							elseif (Enum == 8) then
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 14) then
							if (Enum <= 11) then
								if (Enum == 10) then
									do
										return;
									end
								else
									Stk[Inst[2]] = Inst[3] ~= 0;
								end
							elseif (Enum <= 12) then
								if (Stk[Inst[2]] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 13) then
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							else
								Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
							end
						elseif (Enum <= 17) then
							if (Enum <= 15) then
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							elseif (Enum > 16) then
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
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							end
						elseif (Enum <= 18) then
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
						elseif (Enum > 19) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 31) then
						if (Enum <= 25) then
							if (Enum <= 22) then
								if (Enum > 21) then
									local A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
								elseif (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 23) then
								Stk[Inst[2]] = Inst[3] ~= 0;
							elseif (Enum == 24) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							end
						elseif (Enum <= 28) then
							if (Enum <= 26) then
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							elseif (Enum > 27) then
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							else
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 29) then
							if (Inst[2] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 30) then
							Stk[Inst[2]] = Env[Inst[3]];
						else
							Stk[Inst[2]]();
						end
					elseif (Enum <= 36) then
						if (Enum <= 33) then
							if (Enum > 32) then
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
								local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 34) then
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
								if (Mvm[1] == 75) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						elseif (Enum > 35) then
							Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
						else
							Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
						end
					elseif (Enum <= 39) then
						if (Enum <= 37) then
							Stk[Inst[2]] = Inst[3];
						elseif (Enum == 38) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
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
					elseif (Enum <= 40) then
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum == 41) then
						Stk[Inst[2]] = Upvalues[Inst[3]];
					else
						Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
					end
				elseif (Enum <= 63) then
					if (Enum <= 52) then
						if (Enum <= 47) then
							if (Enum <= 44) then
								if (Enum == 43) then
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = not Stk[Inst[3]];
								end
							elseif (Enum <= 45) then
								do
									return;
								end
							elseif (Enum == 46) then
								local A = Inst[2];
								local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								Stk[Inst[2]] = {};
							end
						elseif (Enum <= 49) then
							if (Enum > 48) then
								Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
							else
								Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
							end
						elseif (Enum <= 50) then
							if (Inst[2] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 51) then
							Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
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
								if (Mvm[1] == 75) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						end
					elseif (Enum <= 57) then
						if (Enum <= 54) then
							if (Enum == 53) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
							end
						elseif (Enum <= 55) then
							Upvalues[Inst[3]] = Stk[Inst[2]];
						elseif (Enum == 56) then
							Stk[Inst[2]]();
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
					elseif (Enum <= 60) then
						if (Enum <= 58) then
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
						elseif (Enum > 59) then
							Stk[Inst[2]] = {};
						elseif (Stk[Inst[2]] < Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 61) then
						Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
					elseif (Enum > 62) then
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					else
						local B = Stk[Inst[4]];
						if B then
							VIP = VIP + 1;
						else
							Stk[Inst[2]] = B;
							VIP = Inst[3];
						end
					end
				elseif (Enum <= 74) then
					if (Enum <= 68) then
						if (Enum <= 65) then
							if (Enum == 64) then
								if (Stk[Inst[2]] < Inst[4]) then
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
						elseif (Enum <= 66) then
							Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
						elseif (Enum > 67) then
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
						else
							Stk[Inst[2]] = Stk[Inst[3]];
						end
					elseif (Enum <= 71) then
						if (Enum <= 69) then
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 70) then
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						else
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
						end
					elseif (Enum <= 72) then
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					elseif (Enum == 73) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Stk[A + 1]));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					else
						Stk[Inst[2]] = Inst[3];
					end
				elseif (Enum <= 79) then
					if (Enum <= 76) then
						if (Enum == 75) then
							Stk[Inst[2]] = Stk[Inst[3]];
						else
							Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
						end
					elseif (Enum <= 77) then
						Stk[Inst[2]] = not Stk[Inst[3]];
					elseif (Enum == 78) then
						if (Stk[Inst[2]] <= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
				elseif (Enum <= 82) then
					if (Enum <= 80) then
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					elseif (Enum > 81) then
						for Idx = Inst[2], Inst[3] do
							Stk[Idx] = nil;
						end
					elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 83) then
					Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
				elseif (Enum == 84) then
					Upvalues[Inst[3]] = Stk[Inst[2]];
				elseif (Inst[2] <= Stk[Inst[4]]) then
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
return VMCall("LOL!0E3Q0003043Q0067616D65030A3Q004765745365727669636503073Q00506C6179657273030B3Q004C6F63616C506C6179657203103Q0055736572496E70757453657276696365028Q00030A3Q00496E707574426567616E03073Q00436F2Q6E65637403043Q007461736B03053Q00737061776E02CD5QCCF43F029A5Q99F93F026Q003940026Q004940002D3Q00121E3Q00013Q0020025Q000200124A000200034Q00353Q0002000200203F00013Q000400121E000200013Q00200200020002000200124A000400054Q00350002000400022Q000B00036Q0052000400053Q00124A000600064Q002F00075Q00203F000800020007002002000800080008000622000A3Q000100012Q004B3Q00034Q001B0008000A000100121E000800093Q00203F00080008000A00062200090001000100022Q004B3Q00034Q004B3Q00014Q000E00080002000100124A0008000B3Q00124A0009000C3Q00124A000A000D3Q00124A000B000E4Q000B000C5Q00121E000D00093Q00203F000D000D000A000622000E00020001000B2Q004B3Q00034Q004B3Q00014Q004B3Q000B4Q004B3Q000C4Q004B3Q00094Q004B3Q00074Q004B3Q00044Q004B3Q00064Q004B3Q00054Q004B3Q000A4Q004B3Q00084Q000E000D000200012Q000A3Q00013Q00033Q00053Q0003073Q004B6579436F646503043Q00456E756D03013Q0050030A3Q006B657972656C65617365025Q0040524002123Q00062B00010011000100010004033Q0011000100203F00023Q000100121E000300023Q00203F00030003000100203F00030003000300061300020011000100030004033Q001100012Q002900026Q002C000200024Q005400026Q002900025Q00062B00020011000100010004033Q0011000100121E000200043Q00124A000300054Q000E0002000200012Q000A3Q00017Q00043Q0003043Q007461736B03043Q0077616974026Q00F03F03053Q007063612Q6C000D3Q00121E3Q00013Q00203F5Q000200124A000100034Q000E3Q000200012Q00297Q0006455Q00013Q0004035Q000100121E3Q00043Q00062200013Q000100012Q00263Q00014Q000E3Q000200010004035Q00012Q000A3Q00013Q00013Q00103Q00030E3Q0046696E6446697273744368696C6403093Q00506C6179657247756903043Q004D61696E030B3Q004361746368696E6742617203053Q004672616D652Q033Q0042617203053Q00436174636803053Q0047722Q656E03073Q00412Q6472652Q73030C3Q006D656D6F72795F777269746503053Q00666C6F6174025Q00E09440026Q00F03F025Q00F09440026Q009540025Q0010954000274Q00297Q0020025Q000100124A000200024Q00353Q000200020006453Q000A00013Q0004033Q000A000100200200013Q000100124A000300034Q00350001000300022Q00433Q00013Q00063E0001000F00013Q0004033Q000F000100203F00013Q000400203F00010001000500203F00010001000600203F00020001000700203F00020002000800203F00020002000900121E0003000A3Q00124A0004000B3Q00204600050002000C00124A0006000D4Q001B00030006000100121E0003000A3Q00124A0004000B3Q00204600050002000E00124A0006000D4Q001B00030006000100121E0003000A3Q00124A0004000B3Q00204600050002000F00124A0006000D4Q001B00030006000100121E0003000A3Q00124A0004000B3Q00204600050002001000124A0006000D4Q001B0003000600012Q000A3Q00017Q002E3Q0003043Q007461736B03043Q007761697402B81E85EB51B89E3F03083Q006B65797072652Q73025Q0040524003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F7450617274026Q00594003053Q007063612Q6C025Q00C0584003093Q00776F726B737061636503043Q0047616D6503073Q00526567696F6E7303093Q004C6F636174696F6E73030E3Q00466F72676F2Q74656E20442Q657003043Q005061727403083Q00506F736974696F6E03013Q005803013Q005A03043Q006D61746803043Q0073717274026Q00104003073Q00566563746F72332Q033Q006E657703013Q005903053Q00547562657303043Q004E616D6503083Q00522Q6F745061727403043Q004669736803063Q00636C69656E74024Q007E842E4103063Q00697061697273030B3Q004765744368696C6472656E03043Q0048656164030B3Q005072696D61727950617274026Q00244003053Q007072696E7403113Q006661696C73616665206C61756E636865642Q01028Q0003053Q0064656C6179026Q003440030D3Q0043752Q72656E7443616D65726103063Q006C2Q6F6B4174025Q008046400066012Q00121E3Q00013Q00203F5Q000200124A000100034Q000E3Q000200012Q00297Q00062B3Q0008000100010004033Q000800010004035Q000100121E3Q00043Q00124A000100054Q000E3Q000200012Q00293Q00013Q00203F5Q000600063E0001001200013Q0004033Q0012000100200200013Q000700124A000300084Q003500010003000200062B00010015000100010004033Q001500010004035Q000100124A000200093Q00121E0003000A3Q00062200043Q000100022Q00263Q00014Q004B3Q00024Q000E0003000200012Q0029000300023Q00060C00020027000100030004033Q002700012Q0029000300033Q00062B00030027000100010004033Q002700012Q000B000300014Q0054000300033Q00121E0003000A3Q00020D000400014Q000E0003000200010004033Q002E0001000E55000B002E000100020004033Q002E00012Q0029000300033Q0006450003002E00013Q0004033Q002E00012Q000B00036Q0054000300034Q0029000300033Q0006450003008600013Q0004033Q0086000100121E0003000C3Q00200200030003000700124A0005000D4Q00350003000500020006450003003B00013Q0004033Q003B000100200200040003000700124A0006000E4Q00350004000600022Q0043000300043Q0006450003004100013Q0004033Q0041000100200200040003000700124A0006000F4Q00350004000600022Q0043000300043Q0006450003004700013Q0004033Q0047000100200200040003000700124A000600104Q00350004000600022Q0043000300043Q00063E0004004C000100030004033Q004C000100200200040003000700124A000600114Q00350004000600020006450004008400013Q0004033Q008400010006450001008400013Q0004033Q0084000100203F00050001001200203F0006000400120006450005008400013Q0004033Q008400010006450006008400013Q0004033Q0084000100203F00070006001300203F0008000500132Q004400070007000800203F00080006001400203F0009000500142Q004400080008000900121E000900153Q00203F0009000900162Q003A000A000700072Q003A000B000800082Q001A000A000A000B2Q001C000900020002000E1D00170084000100090004033Q008400012Q0030000A000700092Q0030000B0008000900121E000C00183Q00203F000C000C001900203F000D000500132Q0029000E00044Q003A000E000A000E2Q001A000D000D000E00203F000E0005001A00203F000F000500142Q0029001000044Q003A0010000B00102Q001A000F000F00102Q0035000C000F0002002Q1000010012000C00121E000C000C3Q00203F000C000C000D00203F000C000C001B002002000C000C00072Q0029000E00013Q00203F000E000E001C2Q0035000C000E0002000645000C008400013Q0004033Q00840001002002000D000C000700124A000F001D4Q0035000D000F0002000645000D008400013Q0004033Q0084000100203F000D000C001D00203F000E00010012002Q10000D0012000E2Q00277Q0004035Q000100121E0003000C3Q00200200030003000700124A0005000D4Q00350003000500020006450003009000013Q0004033Q0090000100200200040003000700124A0006001E4Q00350004000600022Q0043000300043Q0006450003009600013Q0004033Q0096000100200200040003000700124A0006001F4Q00350004000600022Q0043000300043Q00062B0003009A000100010004033Q009A00012Q00277Q0004035Q00012Q0052000400043Q00124A000500203Q00203F00060001001200062B000600A1000100010004033Q00A100012Q00277Q0004035Q000100121E000700213Q0020020008000300222Q0014000800094Q002E00073Q00090004033Q00CB00012Q0029000C00053Q00203F000D000B001C2Q000F000C000C000D00062B000C00CB000100010004033Q00CB0001002002000C000B000700124A000E00234Q0035000C000E000200062B000C00B6000100010004033Q00B60001002002000C000B000700124A000E001D4Q0035000C000E000200062B000C00B6000100010004033Q00B6000100203F000C000B0024000645000C00CB00013Q0004033Q00CB000100203F000D000C0012000645000D00CB00013Q0004033Q00CB000100203F000E000D001300203F000F000600132Q0044000E000E000F00203F000F000D001400203F0010000600142Q0044000F000F001000121E001000153Q00203F0010001000162Q003A0011000E000E2Q003A0012000F000F2Q001A0011001100122Q001C00100002000200062Q001000CB000100050004033Q00CB00012Q0043000500104Q00430004000B3Q000621000700A6000100020004033Q00A60001000645000400602Q013Q0004033Q00602Q01000645000100602Q013Q0004033Q00602Q0100200200070004000700124A000900234Q003500070009000200062B000700DC000100010004033Q00DC000100200200070004000700124A0009001D4Q003500070009000200062B000700DC000100010004033Q00DC000100203F00070004002400063E000800DF000100070004033Q00DF000100203F00080007001200203F000900010012000645000800E400013Q0004033Q00E4000100062B000900E6000100010004033Q00E600012Q00277Q0004035Q000100203F000A0004001C2Q0029000B00063Q000613000A00192Q01000B0004033Q00192Q012Q0029000A00073Q002046000A000A00032Q0054000A00074Q0029000A00083Q000645000A00FE00013Q0004033Q00FE000100203F000A000800132Q0029000B00083Q00203F000B000B00132Q0044000A000A000B00203F000B000800142Q0029000C00083Q00203F000C000C00142Q0044000B000B000C00121E000C00153Q00203F000C000C00162Q003A000D000A000A2Q003A000E000B000B2Q001A000D000D000E2Q001C000C000200022Q0029000A00073Q000E1D0025001D2Q01000A0004033Q001D2Q0100121E000A00263Q00124A000B00274Q000E000A0002000100203F000A0004001C2Q0029000B00053Q00204C000B000A00282Q0052000B000B4Q0054000B00064Q0052000B000B4Q0054000B00084Q0052000400043Q00124A000B00294Q0054000B00073Q00121E000B00013Q00203F000B000B002A00124A000C002B3Q000622000D0002000100022Q00263Q00054Q004B3Q000A4Q001B000B000D00012Q00277Q0004035Q00012Q0027000A5Q0004033Q001D2Q0100203F000A0004001C2Q0054000A00063Q00124A000A00294Q0054000A00074Q0054000800083Q000645000400602Q013Q0004033Q00602Q01000645000900602Q013Q0004033Q00602Q01000645000800602Q013Q0004033Q00602Q0100203F000A0008001300203F000B000900132Q0044000A000A000B00203F000B0008001400203F000C000900142Q0044000B000B000C00121E000C00153Q00203F000C000C00162Q003A000D000A000A2Q003A000E000B000B2Q001A000D000D000E2Q001C000C0002000200121E000D000C3Q00203F000D000D002C00203F000D000D002D00121E000E000C3Q00203F000E000E002C00203F000E000E00122Q0043000F00084Q001B000D000F000100263B000C003D2Q01002E0004033Q003D2Q0100121E000D000A3Q00020D000E00034Q000E000D000200012Q0029000D00093Q00062Q000D004F2Q01000C0004033Q004F2Q012Q0030000D000A000C2Q0030000E000B000C00121E000F00183Q00203F000F000F001900203F0010000900132Q00290011000A4Q003A0011000D00112Q001A00100010001100203F00110009001A00203F0012000900142Q00290013000A4Q003A0013000E00132Q001A0012001200132Q0035000F00120002002Q1000010012000F00121E000D000C3Q00203F000D000D000D00203F000D000D001B002002000D000D00072Q0029000F00013Q00203F000F000F001C2Q0035000D000F0002000645000D00602Q013Q0004033Q00602Q01002002000E000D000700124A0010001D4Q0035000E00100002000645000E00602Q013Q0004033Q00602Q0100203F000E000D001D00203F000F00010012002Q10000E0012000F2Q00277Q0004035Q00012Q00277Q0004035Q00010004035Q00012Q000A3Q00013Q00043Q00093Q0003093Q00506C6179657247756903043Q004D61696E030E3Q0046696E6446697273744368696C6403063Q004F787967656E030C3Q00476574412Q7472696275746503093Q006F6C646F787967656E03083Q00746F6E756D626572025Q00805B40026Q00594000134Q00297Q00203F5Q000100203F5Q00020020025Q000300124A000200044Q00353Q0002000200200200013Q000500124A000300064Q003500010003000200121E000200074Q0043000300014Q001C00020002000200062B0002000F000100010004033Q000F000100124A000200083Q0020240002000200080020530002000200092Q0054000200014Q000A3Q00017Q00063Q0003083Q006B65797072652Q73026Q00564003043Q007461736B03043Q0077616974029A5Q99A93F030A3Q006B657972656C65617365000B3Q00121E3Q00013Q00124A000100024Q000E3Q0002000100121E3Q00033Q00203F5Q000400124A000100054Q000E3Q0002000100121E3Q00063Q00124A000100024Q000E3Q000200012Q000A3Q00017Q00015Q00044Q00298Q0029000100013Q00204C3Q000100012Q000A3Q00017Q00053Q00030B3Q006D6F757365317072652Q7303043Q007461736B03043Q0077616974027B14AE47E17A943F030D3Q006D6F7573653172656C6561736500093Q00121E3Q00014Q00383Q0001000100121E3Q00023Q00203F5Q000300124A000100044Q000E3Q0002000100121E3Q00054Q00383Q000100012Q000A3Q00017Q00", GetFEnv(), ...);