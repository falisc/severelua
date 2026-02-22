--[[
 .____                  ________ ___.    _____                           __                
 |    |    __ _______   \_____  \\_ |___/ ____\_ __  ______ ____ _____ _/  |_  ___________ 
 |    |   |  |  \__  \   /   |   \| __ \   __\  |  \/  ___// ___\\__  \\   __\/  _ \_  __ \
 |    |___|  |  // __ \_/    |    \ \_\ \  | |  |  /\___ \\  \___ / __ \|  | (  <_> )  | \/
 |_______ \____/(____  /\_______  /___  /__| |____//____  >\___  >____  /__|  \____/|__|   
         \/          \/         \/    \/                \/     \/     \/                   
          \_Welcome to LuaObfuscator.com   (Alpha 0.10.9) ~  Much Love, Ferib 

]]--

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
				if (Enum <= 43) then
					if (Enum <= 21) then
						if (Enum <= 10) then
							if (Enum <= 4) then
								if (Enum <= 1) then
									if (Enum == 0) then
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									else
										Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									end
								elseif (Enum <= 2) then
									if (Stk[Inst[2]] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 3) then
									local B = Stk[Inst[4]];
									if B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Upvalues[Inst[3]];
								end
							elseif (Enum <= 7) then
								if (Enum <= 5) then
									local A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
								elseif (Enum == 6) then
									if (Stk[Inst[2]] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Env[Inst[3]];
								end
							elseif (Enum <= 8) then
								if (Inst[2] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 9) then
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							else
								Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
							end
						elseif (Enum <= 15) then
							if (Enum <= 12) then
								if (Enum > 11) then
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
									local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum <= 13) then
								Stk[Inst[2]] = Env[Inst[3]];
							elseif (Enum == 14) then
								Stk[Inst[2]] = Inst[3] ~= 0;
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 18) then
							if (Enum <= 16) then
								Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
							elseif (Enum > 17) then
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							else
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							end
						elseif (Enum <= 19) then
							local B = Stk[Inst[4]];
							if B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						elseif (Enum == 20) then
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
						else
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
						end
					elseif (Enum <= 32) then
						if (Enum <= 26) then
							if (Enum <= 23) then
								if (Enum == 22) then
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
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
							elseif (Enum <= 24) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							elseif (Enum > 25) then
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							else
								Stk[Inst[2]]();
							end
						elseif (Enum <= 29) then
							if (Enum <= 27) then
								Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
							elseif (Enum == 28) then
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
							end
						elseif (Enum <= 30) then
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 31) then
							Stk[Inst[2]] = not Stk[Inst[3]];
						elseif (Stk[Inst[2]] < Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 37) then
						if (Enum <= 34) then
							if (Enum > 33) then
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
							else
								Stk[Inst[2]] = Inst[3] ~= 0;
							end
						elseif (Enum <= 35) then
							if (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 36) then
							local A = Inst[2];
							Stk[A](Stk[A + 1]);
						else
							local A = Inst[2];
							local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 40) then
						if (Enum <= 38) then
							if (Stk[Inst[2]] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 39) then
							if (Stk[Inst[2]] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 41) then
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
					elseif (Enum > 42) then
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
						Upvalues[Inst[3]] = Stk[Inst[2]];
					end
				elseif (Enum <= 65) then
					if (Enum <= 54) then
						if (Enum <= 48) then
							if (Enum <= 45) then
								if (Enum > 44) then
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								else
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								end
							elseif (Enum <= 46) then
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							elseif (Enum > 47) then
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
							elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 51) then
							if (Enum <= 49) then
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							elseif (Enum == 50) then
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
						elseif (Enum <= 52) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						elseif (Enum == 53) then
							Stk[Inst[2]] = Inst[3];
						elseif not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 59) then
						if (Enum <= 56) then
							if (Enum > 55) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							else
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum <= 57) then
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
						elseif (Enum == 58) then
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						else
							Stk[Inst[2]] = {};
						end
					elseif (Enum <= 62) then
						if (Enum <= 60) then
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
								if (Mvm[1] == 86) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						elseif (Enum == 61) then
							VIP = Inst[3];
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 63) then
						Stk[Inst[2]] = Inst[3];
					elseif (Enum > 64) then
						local A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
					else
						do
							return;
						end
					end
				elseif (Enum <= 76) then
					if (Enum <= 70) then
						if (Enum <= 67) then
							if (Enum > 66) then
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
							end
						elseif (Enum <= 68) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						elseif (Enum > 69) then
							if (Stk[Inst[2]] < Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						end
					elseif (Enum <= 73) then
						if (Enum <= 71) then
							Stk[Inst[2]] = {};
						elseif (Enum > 72) then
							Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
						elseif (Inst[2] <= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 74) then
						Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
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
							if (Mvm[1] == 86) then
								Indexes[Idx - 1] = {Stk,Mvm[3]};
							else
								Indexes[Idx - 1] = {Upvalues,Mvm[3]};
							end
							Lupvals[#Lupvals + 1] = Indexes;
						end
						Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
					else
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
					end
				elseif (Enum <= 81) then
					if (Enum <= 78) then
						if (Enum == 77) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							do
								return;
							end
						end
					elseif (Enum <= 79) then
						Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
					elseif (Enum == 80) then
						Upvalues[Inst[3]] = Stk[Inst[2]];
					else
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					end
				elseif (Enum <= 84) then
					if (Enum <= 82) then
						Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
					elseif (Enum > 83) then
						if (Inst[2] < Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Inst[2] < Stk[Inst[4]]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 85) then
					Stk[Inst[2]] = not Stk[Inst[3]];
				elseif (Enum == 86) then
					Stk[Inst[2]] = Stk[Inst[3]];
				else
					local A = Inst[2];
					Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!0E3Q0003043Q0067616D65030A3Q004765745365727669636503073Q00506C6179657273030B3Q004C6F63616C506C6179657203103Q0055736572496E70757453657276696365028Q00026Q004940030A3Q00496E707574426567616E03073Q00436F2Q6E65637403043Q007461736B03053Q00737061776E02CD5QCCF43F029A5Q99F93F026Q003940002E3Q00120D3Q00013Q00203A5Q000200123F000200034Q00343Q0002000200201100013Q000400120D000200013Q00203A00020002000200123F000400054Q00340002000400022Q000E00036Q002C000400053Q00123F000600064Q004700075Q00123F000800063Q00123F000900074Q000E000A5Q002011000B0002000800203A000B000B000900064C000D3Q000100012Q00563Q00034Q0018000B000D000100120D000B000A3Q002011000B000B000B00064C000C0001000100022Q00563Q00034Q00563Q00014Q001A000B0002000100123F000B000C3Q00123F000C000D3Q00123F000D000E3Q00120D000E000A3Q002011000E000E000B00064C000F00020001000B2Q00563Q00034Q00563Q00014Q00563Q00084Q00563Q00094Q00563Q000A4Q00563Q000C4Q00563Q00074Q00563Q00044Q00563Q00064Q00563Q000D4Q00563Q000B4Q001A000E000200012Q004E3Q00013Q00033Q00053Q0003073Q004B6579436F646503043Q00456E756D03013Q0050030A3Q006B657972656C65617365025Q0040524002123Q00063600010011000100010004273Q0011000100201100023Q000100120D000300023Q00201100030003000100201100030003000300062300020011000100030004273Q001100012Q000300026Q001F000200024Q002A00026Q000300025Q00063600020011000100010004273Q0011000100120D000200043Q00123F000300054Q001A0002000200012Q004E3Q00017Q00043Q0003043Q007461736B03043Q0077616974026Q00F03F03053Q007063612Q6C000D3Q00120D3Q00013Q0020115Q000200123F000100034Q001A3Q000200012Q00037Q0006435Q00013Q0004275Q000100120D3Q00043Q00064C00013Q000100012Q00423Q00014Q001A3Q000200010004275Q00012Q004E3Q00013Q00013Q00103Q00030E3Q0046696E6446697273744368696C6403093Q00506C6179657247756903043Q004D61696E030B3Q004361746368696E6742617203053Q004672616D652Q033Q0042617203053Q00436174636803053Q0047722Q656E03073Q00412Q6472652Q73030C3Q006D656D6F72795F777269746503053Q00666C6F6174025Q00E09440026Q00F03F025Q00F09440026Q009540025Q0010954000294Q00037Q00203A5Q000100123F000200024Q00343Q000200020006433Q000A00013Q0004273Q000A000100203A00013Q000100123F000300034Q00340001000300022Q00373Q00013Q0006130001000F00013Q0004273Q000F000100201100013Q00040020110001000100050020110001000100060020110002000100070020110002000200080020110002000200090006430002002800013Q0004273Q0028000100120D0003000A3Q00123F0004000B3Q00202Q00050002000C00123F0006000D4Q001800030006000100120D0003000A3Q00123F0004000B3Q00202Q00050002000E00123F0006000D4Q001800030006000100120D0003000A3Q00123F0004000B3Q00202Q00050002000F00123F0006000D4Q001800030006000100120D0003000A3Q00123F0004000B3Q00202Q00050002001000123F0006000D4Q00180003000600012Q004E3Q00017Q00293Q0003043Q007461736B03043Q007761697402B81E85EB51B89E3F03083Q006B65797072652Q73025Q0040524003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F7450617274028Q0003053Q007063612Q6C026Q005940025Q00C0584003093Q00776F726B737061636503043Q0047616D6503043Q004669736803063Q00636C69656E74024Q007E842E4103083Q00506F736974696F6E03063Q00697061697273030B3Q004765744368696C6472656E03043Q004E616D6503043Q004865616403083Q00522Q6F7450617274030B3Q005072696D6172795061727403013Q005803013Q005A03043Q006D61746803043Q0073717274026Q00244003053Q007072696E7403113Q006661696C73616665206C61756E636865642Q0103053Q0064656C6179026Q003440030D3Q0043752Q72656E7443616D65726103063Q006C2Q6F6B4174025Q0080464003073Q00566563746F72332Q033Q006E657703013Q005903053Q0054756265730003012Q00120D3Q00013Q0020115Q000200123F000100034Q001A3Q000200012Q00037Q0006363Q0008000100010004273Q000800010004275Q000100120D3Q00043Q00123F000100054Q001A3Q000200012Q00033Q00013Q0020115Q00060006130001001200013Q0004273Q0012000100203A00013Q000700123F000300084Q003400010003000200063600010015000100010004273Q001500010004275Q000100123F000200093Q00120D0003000A3Q00064C00043Q000100032Q00423Q00014Q00423Q00024Q00563Q00024Q001A0003000200012Q0003000300023Q000E5300090024000100030004273Q002400012Q0003000300024Q000A00030002000300202200030003000B00063600030025000100010004273Q0025000100123F0003000B4Q0003000400033Q00062800030031000100040004273Q003100012Q0003000400043Q00063600040031000100010004273Q003100012Q000E000400014Q002A000400043Q00120D0004000A3Q000252000500014Q001A0004000200010004273Q00380001000E08000C0038000100030004273Q003800012Q0003000400043Q0006430004003800013Q0004273Q003800012Q000E00046Q002A000400044Q0003000400043Q0006430004004300013Q0004273Q0043000100120D0004000A3Q00064C00050002000100032Q00563Q00014Q00423Q00054Q00423Q00014Q001A0004000200012Q00397Q0004275Q000100120D0004000D3Q00203A00040004000700123F0006000E4Q00340004000600020006430004004D00013Q0004273Q004D000100203A00050004000700123F0007000F4Q00340005000700022Q0037000400053Q0006430004005300013Q0004273Q0053000100203A00050004000700123F000700104Q00340005000700022Q0037000400053Q00063600040057000100010004273Q005700012Q00397Q0004275Q00012Q002C000500053Q00123F000600113Q0020110007000100120006360007005E000100010004273Q005E00012Q00397Q0004275Q000100120D000800133Q00203A0009000400142Q004D0009000A4Q003300083Q000A0004273Q008800012Q0003000D00063Q002011000E000C00152Q0015000D000D000E000636000D0088000100010004273Q0088000100203A000D000C000700123F000F00164Q0034000D000F0002000636000D0073000100010004273Q0073000100203A000D000C000700123F000F00174Q0034000D000F0002000636000D0073000100010004273Q00730001002011000D000C0018000643000D008800013Q0004273Q00880001002011000E000D0012000643000E008800013Q0004273Q00880001002011000F000E00190020110010000700192Q0001000F000F00100020110010000E001A00201100110007001A2Q000100100010001100120D0011001B3Q00201100110011001C2Q00140012000F000F2Q00140013001000102Q00090012001200132Q0005001100020002002Q0600110088000100060004273Q008800012Q0037000600114Q00370005000C3Q00062900080063000100020004273Q00630001000643000500FD00013Q0004273Q00FD0001000643000100FD00013Q0004273Q00FD000100203A00080005000700123F000A00164Q00340008000A000200063600080099000100010004273Q0099000100203A00080005000700123F000A00174Q00340008000A000200063600080099000100010004273Q009900010020110008000500180006130009009C000100080004273Q009C0001002011000900080012002011000A00010012000643000900FD00013Q0004273Q00FD0001000643000A00FD00013Q0004273Q00FD0001002011000B000500152Q0003000C00073Q000623000B00BD0001000C0004273Q00BD00012Q0003000B00083Q00202Q000B000B00032Q002A000B00084Q0003000B00083Q000E53001D00C10001000B0004273Q00C1000100120D000B001E3Q00123F000C001F4Q001A000B000200012Q0003000B00063Q002011000C00050015002049000B000C002000120D000B00013Q002011000B000B002100123F000C00223Q00064C000D0003000100022Q00423Q00064Q00563Q00054Q0018000B000D000100123F000B00094Q002A000B00084Q00397Q0004275Q00010004273Q00C10001002011000B000500152Q002A000B00073Q00123F000B00094Q002A000B00083Q00120D000B000D3Q002011000B000B0023002011000B000B002400120D000C000D3Q002011000C000C0023002011000C000C00122Q0037000D00094Q0018000B000D0001002011000B00090019002011000C000A00192Q0001000B000B000C002011000C0009001A002011000D000A001A2Q0001000C000C000D00120D000D001B3Q002011000D000D001C2Q0014000E000B000B2Q0014000F000C000C2Q0009000E000E000F2Q0005000D00020002002646000D00DA000100250004273Q00DA000100120D000E000A3Q000252000F00044Q001A000E000200012Q0003000E00093Q002Q06000E00EC0001000D0004273Q00EC00012Q000A000E000B000D2Q000A000F000C000D00120D001000263Q0020110010001000270020110011000A00192Q00030012000A4Q00140012000E00122Q00090011001100120020110012000A00280020110013000A001A2Q00030014000A4Q00140014000F00142Q00090013001300142Q003400100013000200104500010012001000120D000E000D3Q002011000E000E000E002011000E000E002900203A000E000E00072Q0003001000013Q0020110010001000152Q0034000E00100002000643000E00FD00013Q0004273Q00FD000100203A000F000E000700123F001100174Q0034000F00110002000643000F00FD00013Q0004273Q00FD0001002011000F000E0017002011001000010012001045000F001200102Q00397Q0004275Q00012Q00397Q0004275Q00010004275Q00012Q004E3Q00013Q00053Q00083Q0003093Q00506C6179657247756903043Q004D61696E030E3Q0046696E6446697273744368696C6403063Q004F787967656E03083Q00746F6E756D626572030C3Q00476574412Q7472696275746503093Q006F6C646F787967656E029Q00164Q00037Q0020115Q00010020115Q000200203A5Q000300123F000200044Q00343Q000200020006433Q001500013Q0004273Q0015000100120D000100053Q00203A00023Q000600123F000400074Q000B000200044Q005700013Q000200063600010010000100010004273Q0010000100123F000100084Q0003000200013Q002Q0600020014000100010004273Q001400012Q002A000100014Q002A000100024Q004E3Q00017Q00063Q0003083Q006B65797072652Q73026Q00564003043Q007461736B03043Q0077616974029A5Q99A93F030A3Q006B657972656C65617365000B3Q00120D3Q00013Q00123F000100024Q001A3Q0002000100120D3Q00033Q0020115Q000400123F000100054Q001A3Q0002000100120D3Q00063Q00123F000100024Q001A3Q000200012Q004E3Q00017Q00133Q0003093Q00776F726B7370616365030E3Q0046696E6446697273744368696C6403043Q0047616D6503073Q00526567696F6E7303093Q004C6F636174696F6E73030E3Q00466F72676F2Q74656E20442Q657003043Q005061727403083Q00506F736974696F6E03013Q005803013Q005A03043Q006D61746803043Q0073717274026Q00104003073Q00566563746F72332Q033Q006E657703013Q005903053Q00547562657303043Q004E616D6503083Q00522Q6F745061727400583Q00120D3Q00013Q00203A5Q000200123F000200034Q00343Q000200020006433Q000A00013Q0004273Q000A000100203A00013Q000200123F000300044Q00340001000300022Q00373Q00013Q0006433Q001000013Q0004273Q0010000100203A00013Q000200123F000300054Q00340001000300022Q00373Q00013Q0006433Q001600013Q0004273Q0016000100203A00013Q000200123F000300064Q00340001000300022Q00373Q00013Q0006130001001B00013Q0004273Q001B000100203A00013Q000200123F000300074Q00340001000300020006430001005700013Q0004273Q005700012Q000300025Q0006430002005700013Q0004273Q005700012Q000300025Q0020110002000200080020110003000100080006430002005700013Q0004273Q005700010006430003005700013Q0004273Q005700010020110004000300090020110005000200092Q000100040004000500201100050003000A00201100060002000A2Q000100050005000600120D0006000B3Q00201100060006000C2Q00140007000400042Q00140008000500052Q00090007000700082Q0005000600020002000E53000D0057000100060004273Q005700012Q000A0007000400062Q000A0008000500062Q000300095Q00120D000A000E3Q002011000A000A000F002011000B000200092Q0003000C00014Q0014000C0007000C2Q0009000B000B000C002011000C00020010002011000D0002000A2Q0003000E00014Q0014000E0008000E2Q0009000D000D000E2Q0034000A000D000200104500090008000A00120D000900013Q00201100090009000300201100090009001100203A0009000900022Q0003000B00023Q002011000B000B00122Q00340009000B00020006430009005700013Q0004273Q0057000100203A000A0009000200123F000C00134Q0034000A000C0002000643000A005700013Q0004273Q00570001002011000A000900132Q0003000B5Q002011000B000B0008001045000A0008000B2Q004E3Q00017Q00023Q0003043Q004E616D652Q00054Q00038Q0003000100013Q0020110001000100010020493Q000100022Q004E3Q00017Q00013Q00030B3Q006D6F75736531636C69636B00033Q00120D3Q00014Q00323Q000100012Q004E3Q00017Q00", GetFEnv(), ...);