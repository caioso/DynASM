----------------------------------------------------------------------------
-- DynASM PPC64 module.
--
-- Copyright (C) 2005-2015 Mike Pall. All rights reserved.
-- See dynasm.lua for full copyright notice.
------------------------------------------------------------------------------

--to be in ppc64.lua
local ppc64 = ppc64
--to be in ppc64.lua

-- Module information:
local _info = {
  arch =	"ppc64",
  description =	"DynASM PPC64 module",
  version =	"1.3.0",
  vernum =	 10300,
  release =	"2011-05-05",
  author =	"Mike Pall",
  license =	"MIT",
}

-- Exported glue functions for the arch-specific module.
local _M = { _info = _info }

-- Cache library functions.
local type, tonumber, pairs, ipairs = type, tonumber, pairs, ipairs
local assert, setmetatable = assert, setmetatable
local _s = string
local sub, format, byte, char = _s.sub, _s.format, _s.byte, _s.char
local match, gmatch = _s.match, _s.gmatch
local concat, sort = table.concat, table.sort

-- Inherited tables and callbacks.
local g_opt, g_arch
local wline, werror, wfatal, wwarn
local bit = bit or require("bit")
local band, shl, shr, bor, sar, bnot = bit.band, bit.lshift, bit.rshift, bit.bor, bit.arshift, bit.bnot
local tohex = bit.tohex

-- Action name list.
-- CHECK: Keep this in sync with the C code!
local action_names = {
  "STOP", "SECTION", "ESC", "REL_EXT",
  "ALIGN", "REL_LG", "LABEL_LG",
  "REL_PC", "LABEL_PC", "IMM",
}

-- Maximum number of section buffer positions for dasm_put().
-- CHECK: Keep this in sync with the C code!
local maxsecpos = 25 -- Keep this low, to avoid excessively long C lines.

-- Action name -> action number.
local map_action = {}
for n,name in ipairs(action_names) do
  map_action[name] = n-1
end

-- Action list buffer.
local actlist = {}

-- Argument list for next dasm_put(). Start with offset 0 into action list.
local actargs = { 0 }

-- Current number of section buffer positions for dasm_put().
local secpos = 1

--Function modes
function_modes = {lsb5 = 1, msb = 2, signed = 1, split_10bit = 1}

------------------------------------------------------------------------------

-- Dump action names and numbers.
local function dumpactions(out)
  out:write("DynASM encoding engine action codes:\n")
  for n,name in ipairs(action_names) do
    local num = map_action[name]
    out:write(format("  %-10s %02X  %d\n", name, num, num))
  end
  out:write("\n")
end

-- Write action list buffer as a huge static C array.
local function writeactions(out, name)
  local nn = #actlist
  if nn == 0 then nn = 1; actlist[0] = map_action.STOP end
  out:write("static const unsigned int ", name, "[", nn, "] = {\n")
  for i = 1,nn-1 do
    assert(out:write("0x", tohex(actlist[i]), ",\n"))
  end
  assert(out:write("0x", tohex(actlist[nn]), "\n};\n\n"))
end

------------------------------------------------------------------------------

-- Add word to action list.
local function wputxw(n)
  if ppc64 then  assert(n >= -0xffffffff and n <= 0xffffffff and n % 1 == 0, "word out of range"..n)
  else assert(n >= 0 and n <= 0xffffffff and n % 1 == 0, "word out of range") end
  actlist[#actlist+1] = n
end

-- Add action to list with optional arg. Advance buffer pos, too.
local function waction(action, val, a, num)
  local w = assert(map_action[action], "bad action name `"..action.."'")
  wputxw(w * 0x10000 + (val or 0))
  if a then actargs[#actargs+1] = a end
  if a or num then secpos = secpos + (num or 1) end
end

-- Flush action list (intervening C code or buffer pos overflow).
local function wflush(term)
  if #actlist == actargs[1] then return end -- Nothing to flush.
  if not term then waction("STOP") end -- Terminate action list.
  wline(format("dasm_put(Dst, %s);", concat(actargs, ", ")), true)
  actargs = { #actlist } -- Actionlist offset is 1st arg to next dasm_put().
  secpos = 1 -- The actionlist offset occupies a buffer position, too.
end

-- Put escaped word.
local function wputw(n)
  if n <= 0xffffff then waction("ESC") end
  wputxw(n)
end

-- Reserve position for word.
local function wpos()
  local pos = #actlist+1
  actlist[pos] = ""
  return pos
end

-- Store word to reserved position.
local function wputpos(pos, n)
  if ppc64 then  assert(n >= -0xffffffff and n <= 0xffffffff and n % 1 == 0, "word out of range"..n)
  else assert(n >= 0 and n <= 0xffffffff and n % 1 == 0, "word out of range") end
  actlist[pos] = n
end

------------------------------------------------------------------------------

-- Global label name -> global label number. With auto assignment on 1st use.
local next_global = 20
local map_global = setmetatable({}, { __index = function(t, name)
  if not match(name, "^[%a_][%w_]*$") then werror("bad global label") end
  local n = next_global
  if n > 2047 then werror("too many global labels") end
  next_global = n + 1
  t[name] = n
  return n
end})

-- Dump global labels.
local function dumpglobals(out, lvl)
  local t = {}
  for name, n in pairs(map_global) do t[n] = name end
  out:write("Global labels:\n")
  for i=20,next_global-1 do
    out:write(format("  %s\n", t[i]))
  end
  out:write("\n")
end

-- Write global label enum.
local function writeglobals(out, prefix)
  local t = {}
  for name, n in pairs(map_global) do t[n] = name end
  out:write("enum {\n")
  for i=20,next_global-1 do
    out:write("  ", prefix, t[i], ",\n")
  end
  out:write("  ", prefix, "_MAX\n};\n")
end

-- Write global label names.
local function writeglobalnames(out, name)
  local t = {}
  for name, n in pairs(map_global) do t[n] = name end
  out:write("static const char *const ", name, "[] = {\n")
  for i=20,next_global-1 do
    out:write("  \"", t[i], "\",\n")
  end
  out:write("  (const char *)0\n};\n")
end

------------------------------------------------------------------------------

-- Extern label name -> extern label number. With auto assignment on 1st use.
local next_extern = 0
local map_extern_ = {}
local map_extern = setmetatable({}, { __index = function(t, name)
  -- No restrictions on the name for now.
  local n = next_extern
  if n > 2047 then werror("too many extern labels") end
  next_extern = n + 1
  t[name] = n
  map_extern_[n] = name
  return n
end})

-- Dump extern labels.
local function dumpexterns(out, lvl)
  out:write("Extern labels:\n")
  for i=0,next_extern-1 do
    out:write(format("  %s\n", map_extern_[i]))
  end
  out:write("\n")
end

-- Write extern label names.
local function writeexternnames(out, name)
  out:write("static const char *const ", name, "[] = {\n")
  for i=0,next_extern-1 do
    out:write("  \"", map_extern_[i], "\",\n")
  end
  out:write("  (const char *)0\n};\n")
end

------------------------------------------------------------------------------

-- Arch-specific maps.
local map_archdef = { sp = "r1" } -- Ext. register name -> int. name.

local map_type = {}		-- Type name -> { ctype, reg }
local ctypenum = 0		-- Type number (for Dt... macros).

-- Reverse defines for registers.
function _M.revdef(s)
  if s == "r1" then return "sp" end
  return s
end

local map_cond = {
  lt = 0, gt = 1, eq = 2, so = 3,
  ge = 4, le = 5, ne = 6, ns = 7,
}

------------------------------------------------------------------------------

-- Template strings for PPC64 instructions.
local map_op = {
  tdi_3 =	"08000000ARI",
  twi_3 =	"0c000000ARI",
  mulli_3 =	"1c000000RRI",
  subfic_3 =	"20000000RRI",
  cmplwi_3 =	"28000000XRU",
  cmplwi_2 =	"28000000-RU",
  cmpldi_3 =	"28200000XRU",
  cmpldi_2 =	"28200000-RU",
  cmpwi_3 =	"2c000000XRI",
  cmpwi_2 =	"2c000000-RI",
  cmpdi_3 =	"2c200000XRI",
  cmpdi_2 =	"2c200000-RI",
  addic_3 =	"30000000RRI",
  ["addic._3"] = "34000000RRI",
  addi_3 =	"38000000RR0I",
  li_2 =	"38000000RI",
  la_2 =	"38000000RD",
  addis_3 =	"3c000000RR0I",
  lis_2 =	"3c000000RI",
  lus_2 =	"3c000000RU",
  bc_3 =	"40000000AAK",
  bcl_3 =	"40000001AAK",
  bdnz_1 =	"42000000K",
  bdz_1 =	"42400000K",
  sc_0 =	"44000000",
  b_1 =		"48000000J",
  bl_1 =	"48000001J",
  rlwimi_5 =	"50000000RR~AAA.",
  rlwinm_5 =	"54000000RR~AAA.",
  rlwnm_5 =	"5c000000RR~RAA.",
  ori_3 =	"60000000RR~U",
  nop_0 =	"60000000",
  oris_3 =	"64000000RR~U",
  xori_3 =	"68000000RR~U",
  xoris_3 =	"6c000000RR~U",
  ["andi._3"] =	"70000000RR~U",
  ["andis._3"] = "74000000RR~U",
  lwz_2 =	"80000000RD",
  lwzu_2 =	"84000000RD",
  lbz_2 =	"88000000RD",
  lbzu_2 =	"8c000000RD",
  stw_2 =	"90000000RD",
  stwu_2 =	"94000000RD",
  stb_2 =	"98000000RD",
  stbu_2 =	"9c000000RD",
  lhz_2 =	"a0000000RD",
  lhzu_2 =	"a4000000RD",
  lha_2 =	"a8000000RD",
  lhau_2 =	"ac000000RD",
  sth_2 =	"b0000000RD",
  sthu_2 =	"b4000000RD",
  lmw_2 =	"b8000000RD",
  stmw_2 =	"bc000000RD",
  lfs_2 =	"c0000000FD",
  lfsu_2 =	"c4000000FD",
  lfd_2 =	"c8000000FD",
  lfdu_2 =	"cc000000FD",
  stfs_2 =	"d0000000FD",
  stfsu_2 =	"d4000000FD",
  stfd_2 =	"d8000000FD",
  stfdu_2 =	"dc000000FD",
  ld_2 =	"e8000000RD", -- NYI: displacement must be divisible by 4.
  ldu_2 =	"e8000001RD",
  lwa_2 =	"e8000002RD",
  std_2 =	"f8000000RD",
  stdu_2 =	"f8000001RD",

  -- Primary opcode 19:
  mcrf_2 =	"4c000000XX",
  isync_0 =	"4c00012c",
  crnor_3 =	"4c000042CCC",
  crnot_2 =	"4c000042CC=",
  crandc_3 =	"4c000102CCC",
  crxor_3 =	"4c000182CCC",
  crclr_1 =	"4c000182C==",
  crnand_3 =	"4c0001c2CCC",
  crand_3 =	"4c000202CCC",
  creqv_3 =	"4c000242CCC",
  crset_1 =	"4c000242C==",
  crorc_3 =	"4c000342CCC",
  cror_3 =	"4c000382CCC",
  crmove_2 =	"4c000382CC=",
  bclr_2 =	"4c000020AA",
  bclrl_2 =	"4c000021AA",
  bcctr_2 =	"4c000420AA",
  bcctrl_2 =	"4c000421AA",
  blr_0 =	"4e800020",
  blrl_0 =	"4e800021",
  bctr_0 =	"4e800420",
  bctrl_0 =	"4e800421",

  -- Primary opcode 31:
  cmpw_3 =	"7c000000XRR",
  cmpw_2 =	"7c000000-RR",
  cmpd_3 =	"7c200000XRR",
  cmpd_2 =	"7c200000-RR",
  tw_3 =	"7c000008ARR",
  subfc_3 =	"7c000010RRR.",
  subc_3 =	"7c000010RRR~.",
  mulhdu_3 =	"7c000012RRR.",
  addc_3 =	"7c000014RRR.",
  mulhwu_3 =	"7c000016RRR.",
  isel_4 =	"7c00001eRRRC",
  isellt_3 =	"7c00001eRRR",
  iselgt_3 =	"7c00005eRRR",
  iseleq_3 =	"7c00009eRRR",
  mfcr_1 =	"7c000026R",
  mtcrf_2 =	"7c000120GR",
  -- NYI: mtocrf, mfocrf
  lwarx_3 =	"7c000028RR0R",
  ldx_3 =	"7c00002aRR0R",
  lwzx_3 =	"7c00002eRR0R",
  slw_3 =	"7c000030RR~R.",
  cntlzw_2 =	"7c000034RR~",
  sld_3 =	"7c000036RR~R.",
  and_3 =	"7c000038RR~R.",
  cmplw_3 =	"7c000040XRR",
  cmplw_2 =	"7c000040-RR",
  cmpld_3 =	"7c200040XRR",
  cmpld_2 =	"7c200040-RR",
  subf_3 =	"7c000050RRR.",
  sub_3 =	"7c000050RRR~.",
  ldux_3 =	"7c00006aRR0R",
  dcbst_2 =	"7c00006c-RR",
  lwzux_3 =	"7c00006eRR0R",
  cntlzd_2 =	"7c000074RR~",
  andc_3 =	"7c000078RR~R.",
  td_3 =	"7c000088ARR",
  mulhd_3 =	"7c000092RRR.",
  mulhw_3 =	"7c000096RRR.",
  ldarx_3 =	"7c0000a8RR0R",
  dcbf_2 =	"7c0000ac-RR",
  lbzx_3 =	"7c0000aeRR0R",
  neg_2 =	"7c0000d0RR.",
  lbzux_3 =	"7c0000eeRR0R",
  popcntb_2 =	"7c0000f4RR~",
  not_2 =	"7c0000f8RR~%.",
  nor_3 =	"7c0000f8RR~R.",
  subfe_3 =	"7c000110RRR.",
  sube_3 =	"7c000110RRR~.",
  adde_3 =	"7c000114RRR.",
  stdx_3 =	"7c00012aRR0R",
  stwcx_3 =	"7c00012cRR0R.",
  stwx_3 =	"7c00012eRR0R",
  prtyw_2 =	"7c000134RR~",
  stdux_3 =	"7c00016aRR0R",
  stwux_3 =	"7c00016eRR0R",
  prtyd_2 =	"7c000174RR~",
  subfze_2 =	"7c000190RR.",
  addze_2 =	"7c000194RR.",
  stdcx_3 =	"7c0001acRR0R.",
  stbx_3 =	"7c0001aeRR0R",
  subfme_2 =	"7c0001d0RR.",
  mulld_3 =	"7c0001d2RRR.",
  addme_2 =	"7c0001d4RR.",
  mullw_3 =	"7c0001d6RRR.",
  dcbtst_2 =	"7c0001ec-RR",
  stbux_3 =	"7c0001eeRR0R",
  add_3 =	"7c000214RRR.",
  dcbt_2 =	"7c00022c-RR",
  lhzx_3 =	"7c00022eRR0R",
  eqv_3 =	"7c000238RR~R.",
  eciwx_3 =	"7c00026cRR0R",
  lhzux_3 =	"7c00026eRR0R",
  xor_3 =	"7c000278RR~R.",
  mfspefscr_1 =	"7c0082a6R",
  mfxer_1 =	"7c0102a6R",
  mflr_1 =	"7c0802a6R",
  mfctr_1 =	"7c0902a6R",
  lwax_3 =	"7c0002aaRR0R",
  lhax_3 =	"7c0002aeRR0R",
  mftb_1 =	"7c0c42a6R",
  mftbu_1 =	"7c0d42a6R",
  lwaux_3 =	"7c0002eaRR0R",
  lhaux_3 =	"7c0002eeRR0R",
  sthx_3 =	"7c00032eRR0R",
  orc_3 =	"7c000338RR~R.",
  ecowx_3 =	"7c00036cRR0R",
  sthux_3 =	"7c00036eRR0R",
  or_3 =	"7c000378RR~R.",
  mr_2 =	"7c000378RR~%.",
  divdu_3 =	"7c000392RRR.",
  divwu_3 =	"7c000396RRR.",
  mtspefscr_1 =	"7c0083a6R",
  mtxer_1 =	"7c0103a6R",
  mtlr_1 =	"7c0803a6R",
  mtctr_1 =	"7c0903a6R",
  dcbi_2 =	"7c0003ac-RR",
  nand_3 =	"7c0003b8RR~R.",
  divd_3 =	"7c0003d2RRR.",
  divw_3 =	"7c0003d6RRR.",
  cmpb_3 =	"7c0003f8RR~R.",
  mcrxr_1 =	"7c000400X",
  subfco_3 =	"7c000410RRR.",
  subco_3 =	"7c000410RRR~.",
  addco_3 =	"7c000414RRR.",
  ldbrx_3 =	"7c000428RR0R",
  lswx_3 =	"7c00042aRR0R",
  lwbrx_3 =	"7c00042cRR0R",
  lfsx_3 =	"7c00042eFR0R",
  srw_3 =	"7c000430RR~R.",
  srd_3 =	"7c000436RR~R.",
  subfo_3 =	"7c000450RRR.",
  subo_3 =	"7c000450RRR~.",
  lfsux_3 =	"7c00046eFR0R",
  lswi_3 =	"7c0004aaRR0A",
  sync_0 =	"7c0004ac",
  lwsync_0 =	"7c2004ac",
  ptesync_0 =	"7c4004ac",
  lfdx_3 =	"7c0004aeFR0R",
  nego_2 =	"7c0004d0RR.",
  lfdux_3 =	"7c0004eeFR0R",
  subfeo_3 =	"7c000510RRR.",
  subeo_3 =	"7c000510RRR~.",
  addeo_3 =	"7c000514RRR.",
  stdbrx_3 =	"7c000528RR0R",
  stswx_3 =	"7c00052aRR0R",
  stwbrx_3 =	"7c00052cRR0R",
  stfsx_3 =	"7c00052eFR0R",
  stfsux_3 =	"7c00056eFR0R",
  subfzeo_2 =	"7c000590RR.",
  addzeo_2 =	"7c000594RR.",
  stswi_3 =	"7c0005aaRR0A",
  stfdx_3 =	"7c0005aeFR0R",
  subfmeo_2 =	"7c0005d0RR.",
  mulldo_3 =	"7c0005d2RRR.",
  addmeo_2 =	"7c0005d4RR.",
  mullwo_3 =	"7c0005d6RRR.",
  dcba_2 =	"7c0005ec-RR",
  stfdux_3 =	"7c0005eeFR0R",
  addo_3 =	"7c000614RRR.",
  lhbrx_3 =	"7c00062cRR0R",
  sraw_3 =	"7c000630RR~R.",
  srad_3 =	"7c000634RR~R.",
  srawi_3 =	"7c000670RR~A.",
  eieio_0 =	"7c0006ac",
  lfiwax_3 =	"7c0006aeFR0R",
  sthbrx_3 =	"7c00072cRR0R",
  extsh_2 =	"7c000734RR~.",
  extsb_2 =	"7c000774RR~.",
  divduo_3 =	"7c000792RRR.",
  divwou_3 =	"7c000796RRR.",
  icbi_2 =	"7c0007ac-RR",
  stfiwx_3 =	"7c0007aeFR0R",
  extsw_2 =	"7c0007b4RR~.",
  divdo_3 =	"7c0007d2RRR.",
  divwo_3 =	"7c0007d6RRR.",
  dcbz_2 =	"7c0007ec-RR",

  -- Primary opcode 59:
  fdivs_3 =	"ec000024FFF.",
  fsubs_3 =	"ec000028FFF.",
  fadds_3 =	"ec00002aFFF.",
  fsqrts_2 =	"ec00002cF-F.",
  fres_2 =	"ec000030F-F.",
  fmuls_3 =	"ec000032FF-F.",
  frsqrtes_2 =	"ec000034F-F.",
  fmsubs_4 =	"ec000038FFFF~.",
  fmadds_4 =	"ec00003aFFFF~.",
  fnmsubs_4 =	"ec00003cFFFF~.",
  fnmadds_4 =	"ec00003eFFFF~.",

  -- Primary opcode 63:
  fdiv_3 =	"fc000024FFF.",
  fsub_3 =	"fc000028FFF.",
  fadd_3 =	"fc00002aFFF.",
  fsqrt_2 =	"fc00002cF-F.",
  fsel_4 =	"fc00002eFFFF~.",
  fre_2 =	"fc000030F-F.",
  fmul_3 =	"fc000032FF-F.",
  frsqrte_2 =	"fc000034F-F.",
  fmsub_4 =	"fc000038FFFF~.",
  fmadd_4 =	"fc00003aFFFF~.",
  fnmsub_4 =	"fc00003cFFFF~.",
  fnmadd_4 =	"fc00003eFFFF~.",
  fcmpu_3 =	"fc000000XFF",
  fcpsgn_3 =	"fc000010FFF.",
  fcmpo_3 =	"fc000040XFF",
  mtfsb1_1 =	"fc00004cA",
  fneg_2 =	"fc000050F-F.",
  mcrfs_2 =	"fc000080XX",
  mtfsb0_1 =	"fc00008cA",
  fmr_2 =	"fc000090F-F.",
  frsp_2 =	"fc000018F-F.",
  fctiw_2 =	"fc00001cF-F.",
  fctiwz_2 =	"fc00001eF-F.",
  mtfsfi_2 =	"fc00010cAA", -- NYI: upshift.
  fnabs_2 =	"fc000110F-F.",
  fabs_2 =	"fc000210F-F.",
  frin_2 =	"fc000310F-F.",
  friz_2 =	"fc000350F-F.",
  frip_2 =	"fc000390F-F.",
  frim_2 =	"fc0003d0F-F.",
  mffs_1 =	"fc00048eF.",
  -- NYI: mtfsf, mtfsb0, mtfsb1.
  fctid_2 =	"fc00065cF-F.",
  fctidz_2 =	"fc00065eF-F.",
  fcfid_2 =	"fc00069cF-F.",

  -- Primary opcode 4, SPE APU extension:
  evaddw_3 =		"10000200RRR",
  evaddiw_3 =		"10000202RAR~",
  evsubw_3 =		"10000204RRR~",
  evsubiw_3 =		"10000206RAR~",
  evabs_2 =		"10000208RR",
  evneg_2 =		"10000209RR",
  evextsb_2 =		"1000020aRR",
  evextsh_2 =		"1000020bRR",
  evrndw_2 =		"1000020cRR",
  evcntlzw_2 =		"1000020dRR",
  evcntlsw_2 =		"1000020eRR",
  brinc_3 =		"1000020fRRR",
  evand_3 =		"10000211RRR",
  evandc_3 =		"10000212RRR",
  evxor_3 =		"10000216RRR",
  evor_3 =		"10000217RRR",
  evmr_2 =		"10000217RR=",
  evnor_3 =		"10000218RRR",
  evnot_2 =		"10000218RR=",
  eveqv_3 =		"10000219RRR",
  evorc_3 =		"1000021bRRR",
  evnand_3 =		"1000021eRRR",
  evsrwu_3 =		"10000220RRR",
  evsrws_3 =		"10000221RRR",
  evsrwiu_3 =		"10000222RRA",
  evsrwis_3 =		"10000223RRA",
  evslw_3 =		"10000224RRR",
  evslwi_3 =		"10000226RRA",
  evrlw_3 =		"10000228RRR",
  evsplati_2 =		"10000229RS",
  evrlwi_3 =		"1000022aRRA",
  evsplatfi_2 =		"1000022bRS",
  evmergehi_3 =		"1000022cRRR",
  evmergelo_3 =		"1000022dRRR",
  evcmpgtu_3 =		"10000230XRR",
  evcmpgtu_2 =		"10000230-RR",
  evcmpgts_3 =		"10000231XRR",
  evcmpgts_2 =		"10000231-RR",
  evcmpltu_3 =		"10000232XRR",
  evcmpltu_2 =		"10000232-RR",
  evcmplts_3 =		"10000233XRR",
  evcmplts_2 =		"10000233-RR",
  evcmpeq_3 =		"10000234XRR",
  evcmpeq_2 =		"10000234-RR",
  evsel_4 =		"10000278RRRW",
  evsel_3 =		"10000278RRR",
  evfsadd_3 =		"10000280RRR",
  evfssub_3 =		"10000281RRR",
  evfsabs_2 =		"10000284RR",
  evfsnabs_2 =		"10000285RR",
  evfsneg_2 =		"10000286RR",
  evfsmul_3 =		"10000288RRR",
  evfsdiv_3 =		"10000289RRR",
  evfscmpgt_3 =		"1000028cXRR",
  evfscmpgt_2 =		"1000028c-RR",
  evfscmplt_3 =		"1000028dXRR",
  evfscmplt_2 =		"1000028d-RR",
  evfscmpeq_3 =		"1000028eXRR",
  evfscmpeq_2 =		"1000028e-RR",
  evfscfui_2 =		"10000290R-R",
  evfscfsi_2 =		"10000291R-R",
  evfscfuf_2 =		"10000292R-R",
  evfscfsf_2 =		"10000293R-R",
  evfsctui_2 =		"10000294R-R",
  evfsctsi_2 =		"10000295R-R",
  evfsctuf_2 =		"10000296R-R",
  evfsctsf_2 =		"10000297R-R",
  evfsctuiz_2 =		"10000298R-R",
  evfsctsiz_2 =		"1000029aR-R",
  evfststgt_3 =		"1000029cXRR",
  evfststgt_2 =		"1000029c-RR",
  evfststlt_3 =		"1000029dXRR",
  evfststlt_2 =		"1000029d-RR",
  evfststeq_3 =		"1000029eXRR",
  evfststeq_2 =		"1000029e-RR",
  efsadd_3 =		"100002c0RRR",
  efssub_3 =		"100002c1RRR",
  efsabs_2 =		"100002c4RR",
  efsnabs_2 =		"100002c5RR",
  efsneg_2 =		"100002c6RR",
  efsmul_3 =		"100002c8RRR",
  efsdiv_3 =		"100002c9RRR",
  efscmpgt_3 =		"100002ccXRR",
  efscmpgt_2 =		"100002cc-RR",
  efscmplt_3 =		"100002cdXRR",
  efscmplt_2 =		"100002cd-RR",
  efscmpeq_3 =		"100002ceXRR",
  efscmpeq_2 =		"100002ce-RR",
  efscfd_2 =		"100002cfR-R",
  efscfui_2 =		"100002d0R-R",
  efscfsi_2 =		"100002d1R-R",
  efscfuf_2 =		"100002d2R-R",
  efscfsf_2 =		"100002d3R-R",
  efsctui_2 =		"100002d4R-R",
  efsctsi_2 =		"100002d5R-R",
  efsctuf_2 =		"100002d6R-R",
  efsctsf_2 =		"100002d7R-R",
  efsctuiz_2 =		"100002d8R-R",
  efsctsiz_2 =		"100002daR-R",
  efststgt_3 =		"100002dcXRR",
  efststgt_2 =		"100002dc-RR",
  efststlt_3 =		"100002ddXRR",
  efststlt_2 =		"100002dd-RR",
  efststeq_3 =		"100002deXRR",
  efststeq_2 =		"100002de-RR",
  efdadd_3 =		"100002e0RRR",
  efdsub_3 =		"100002e1RRR",
  efdcfuid_2 =		"100002e2R-R",
  efdcfsid_2 =		"100002e3R-R",
  efdabs_2 =		"100002e4RR",
  efdnabs_2 =		"100002e5RR",
  efdneg_2 =		"100002e6RR",
  efdmul_3 =		"100002e8RRR",
  efddiv_3 =		"100002e9RRR",
  efdctuidz_2 =		"100002eaR-R",
  efdctsidz_2 =		"100002ebR-R",
  efdcmpgt_3 =		"100002ecXRR",
  efdcmpgt_2 =		"100002ec-RR",
  efdcmplt_3 =		"100002edXRR",
  efdcmplt_2 =		"100002ed-RR",
  efdcmpeq_3 =		"100002eeXRR",
  efdcmpeq_2 =		"100002ee-RR",
  efdcfs_2 =		"100002efR-R",
  efdcfui_2 =		"100002f0R-R",
  efdcfsi_2 =		"100002f1R-R",
  efdcfuf_2 =		"100002f2R-R",
  efdcfsf_2 =		"100002f3R-R",
  efdctui_2 =		"100002f4R-R",
  efdctsi_2 =		"100002f5R-R",
  efdctuf_2 =		"100002f6R-R",
  efdctsf_2 =		"100002f7R-R",
  efdctuiz_2 =		"100002f8R-R",
  efdctsiz_2 =		"100002faR-R",
  efdtstgt_3 =		"100002fcXRR",
  efdtstgt_2 =		"100002fc-RR",
  efdtstlt_3 =		"100002fdXRR",
  efdtstlt_2 =		"100002fd-RR",
  efdtsteq_3 =		"100002feXRR",
  efdtsteq_2 =		"100002fe-RR",
  evlddx_3 =		"10000300RR0R",
  evldd_2 =		"10000301R8",
  evldwx_3 =		"10000302RR0R",
  evldw_2 =		"10000303R8",
  evldhx_3 =		"10000304RR0R",
  evldh_2 =		"10000305R8",
  evlwhex_3 =		"10000310RR0R",
  evlwhe_2 =		"10000311R4",
  evlwhoux_3 =		"10000314RR0R",
  evlwhou_2 =		"10000315R4",
  evlwhosx_3 =		"10000316RR0R",
  evlwhos_2 =		"10000317R4",
  evstddx_3 =		"10000320RR0R",
  evstdd_2 =		"10000321R8",
  evstdwx_3 =		"10000322RR0R",
  evstdw_2 =		"10000323R8",
  evstdhx_3 =		"10000324RR0R",
  evstdh_2 =		"10000325R8",
  evstwhex_3 =		"10000330RR0R",
  evstwhe_2 =		"10000331R4",
  evstwhox_3 =		"10000334RR0R",
  evstwho_2 =		"10000335R4",
  evstwwex_3 =		"10000338RR0R",
  evstwwe_2 =		"10000339R4",
  evstwwox_3 =		"1000033cRR0R",
  evstwwo_2 =		"1000033dR4",
  evmhessf_3 =		"10000403RRR",
  evmhossf_3 =		"10000407RRR",
  evmheumi_3 =		"10000408RRR",
  evmhesmi_3 =		"10000409RRR",
  evmhesmf_3 =		"1000040bRRR",
  evmhoumi_3 =		"1000040cRRR",
  evmhosmi_3 =		"1000040dRRR",
  evmhosmf_3 =		"1000040fRRR",
  evmhessfa_3 =		"10000423RRR",
  evmhossfa_3 =		"10000427RRR",
  evmheumia_3 =		"10000428RRR",
  evmhesmia_3 =		"10000429RRR",
  evmhesmfa_3 =		"1000042bRRR",
  evmhoumia_3 =		"1000042cRRR",
  evmhosmia_3 =		"1000042dRRR",
  evmhosmfa_3 =		"1000042fRRR",
  evmwhssf_3 =		"10000447RRR",
  evmwlumi_3 =		"10000448RRR",
  evmwhumi_3 =		"1000044cRRR",
  evmwhsmi_3 =		"1000044dRRR",
  evmwhsmf_3 =		"1000044fRRR",
  evmwssf_3 =		"10000453RRR",
  evmwumi_3 =		"10000458RRR",
  evmwsmi_3 =		"10000459RRR",
  evmwsmf_3 =		"1000045bRRR",
  evmwhssfa_3 =		"10000467RRR",
  evmwlumia_3 =		"10000468RRR",
  evmwhumia_3 =		"1000046cRRR",
  evmwhsmia_3 =		"1000046dRRR",
  evmwhsmfa_3 =		"1000046fRRR",
  evmwssfa_3 =		"10000473RRR",
  evmwumia_3 =		"10000478RRR",
  evmwsmia_3 =		"10000479RRR",
  evmwsmfa_3 =		"1000047bRRR",
  evmra_2 =		"100004c4RR",
  evdivws_3 =		"100004c6RRR",
  evdivwu_3 =		"100004c7RRR",
  evmwssfaa_3 =		"10000553RRR",
  evmwumiaa_3 =		"10000558RRR",
  evmwsmiaa_3 =		"10000559RRR",
  evmwsmfaa_3 =		"1000055bRRR",
  evmwssfan_3 =		"100005d3RRR",
  evmwumian_3 =		"100005d8RRR",
  evmwsmian_3 =		"100005d9RRR",
  evmwsmfan_3 =		"100005dbRRR",
  evmergehilo_3 =	"1000022eRRR",
  evmergelohi_3 =	"1000022fRRR",
  evlhhesplatx_3 =	"10000308RR0R",
  evlhhesplat_2 =	"10000309R2",
  evlhhousplatx_3 =	"1000030cRR0R",
  evlhhousplat_2 =	"1000030dR2",
  evlhhossplatx_3 =	"1000030eRR0R",
  evlhhossplat_2 =	"1000030fR2",
  evlwwsplatx_3 =	"10000318RR0R",
  evlwwsplat_2 =	"10000319R4",
  evlwhsplatx_3 =	"1000031cRR0R",
  evlwhsplat_2 =	"1000031dR4",
  evaddusiaaw_2 =	"100004c0RR",
  evaddssiaaw_2 =	"100004c1RR",
  evsubfusiaaw_2 =	"100004c2RR",
  evsubfssiaaw_2 =	"100004c3RR",
  evaddumiaaw_2 =	"100004c8RR",
  evaddsmiaaw_2 =	"100004c9RR",
  evsubfumiaaw_2 =	"100004caRR",
  evsubfsmiaaw_2 =	"100004cbRR",
  evmheusiaaw_3 =	"10000500RRR",
  evmhessiaaw_3 =	"10000501RRR",
  evmhessfaaw_3 =	"10000503RRR",
  evmhousiaaw_3 =	"10000504RRR",
  evmhossiaaw_3 =	"10000505RRR",
  evmhossfaaw_3 =	"10000507RRR",
  evmheumiaaw_3 =	"10000508RRR",
  evmhesmiaaw_3 =	"10000509RRR",
  evmhesmfaaw_3 =	"1000050bRRR",
  evmhoumiaaw_3 =	"1000050cRRR",
  evmhosmiaaw_3 =	"1000050dRRR",
  evmhosmfaaw_3 =	"1000050fRRR",
  evmhegumiaa_3 =	"10000528RRR",
  evmhegsmiaa_3 =	"10000529RRR",
  evmhegsmfaa_3 =	"1000052bRRR",
  evmhogumiaa_3 =	"1000052cRRR",
  evmhogsmiaa_3 =	"1000052dRRR",
  evmhogsmfaa_3 =	"1000052fRRR",
  evmwlusiaaw_3 =	"10000540RRR",
  evmwlssiaaw_3 =	"10000541RRR",
  evmwlumiaaw_3 =	"10000548RRR",
  evmwlsmiaaw_3 =	"10000549RRR",
  evmheusianw_3 =	"10000580RRR",
  evmhessianw_3 =	"10000581RRR",
  evmhessfanw_3 =	"10000583RRR",
  evmhousianw_3 =	"10000584RRR",
  evmhossianw_3 =	"10000585RRR",
  evmhossfanw_3 =	"10000587RRR",
  evmheumianw_3 =	"10000588RRR",
  evmhesmianw_3 =	"10000589RRR",
  evmhesmfanw_3 =	"1000058bRRR",
  evmhoumianw_3 =	"1000058cRRR",
  evmhosmianw_3 =	"1000058dRRR",
  evmhosmfanw_3 =	"1000058fRRR",
  evmhegumian_3 =	"100005a8RRR",
  evmhegsmian_3 =	"100005a9RRR",
  evmhegsmfan_3 =	"100005abRRR",
  evmhogumian_3 =	"100005acRRR",
  evmhogsmian_3 =	"100005adRRR",
  evmhogsmfan_3 =	"100005afRRR",
  evmwlusianw_3 =	"100005c0RRR",
  evmwlssianw_3 =	"100005c1RRR",
  evmwlumianw_3 =	"100005c8RRR",
  evmwlsmianw_3 =	"100005c9RRR",

  --PPC64 INSTRUCTIONS0
 
  -- Opcode 4
  vaddubm_3 =		"10000000VVV",
  vmaxub_3 =		"10000002VVV",
  vrlb_3 =		"10000004VVV",
  vcmpequb_3 =		"10000006VVV",
  vmuloub_3 =		"10000008VVV",
  vaddfp_3 =		"1000000aVVV",
  vmrghb_3 =		"1000000cVVV",
  vpkuhum_3 =		"1000000eVVV",
  mulhhwu_3 =		"10000010RRR.",
  machhwu_3 =		"10000018RRR.",
  vmhaddshs_4 =		"10000020VVVV",
  vmhraddshs_4 =	"10000021VVVV",
  vmladduhm_4 =		"10000022VVVV",
  vmsumubm_4 =		"10000024VVVV",
  vmsummbm_4 =		"10000025VVVV",
  vmsumuhm_4 =		"10000026VVVV",
  vmsumuhs_4 =		"10000027VVVV",
  vmsumshm_4 =		"10000028VVVV",
  vmsumshs_4 =		"10000029VVVV",
  vsel_4 =		"1000002aVVVV",
  vperm_4 =		"1000002bVVVV",
  vsldoi_4 =		"1000002cVVV:P",
  vpermxor_4 =		"1000002dVVVV",
  vmaddfp_4 =		"1000002eVVVV~",
  vnmsubfp_4 =		"1000002fVVVV~",
  vaddeuqm_4 =		"1000003cVVVV",
  vaddecuq_4 =		"1000003dVVVV",
  vsubeuqm_4 =		"1000003eVVVV",
  vsubecuq_4 =		"1000003fVVVV",
  vadduhm_3 =		"10000040VVV",
  vmaxuh_3 =		"10000042VVV",
  vrlh_3 =		"10000044VVV",
  vcmpequh_3 =		"10000046VVV",
  vmulouh_3 =		"10000048VVV",
  vsubfp_3 =		"1000004aVVV",
  vmrghh_3 =		"1000004cVVV",
  vpkuwum_3 =		"1000004eVVV",
  mulhhw_3 =		"10000050RRR.",
  nmachhw_3 =		"1000005cRRR.",
  vadduwm_3 =		"10000080VVV",
  vmaxuw_3 =		"10000082VVV",
  vrlw_3 =		"10000084VVV",
  vcmpequw_3 =		"10000086VVV",
  vmulouw_3 =		"10000088VVV",
  vmuluwm_3 =		"10000089VVV",
  vmrghw_3 =		"1000008cVVV",
  vpkuhus_3 =		"1000008eVVV",
  machhwsu_3 =		"10000098RRR.",
  vaddudm_3 =		"100000c0VVV",
  vmaxud_3 =		"100000c2VVV",
  vrld_3 =		"100000c4VVV",
  vcmpeqfp_3 =		"100000c6VVV",
  vcmpequd_3 =		"100000c7VVV",
  vpkuwus_3 =		"100000ceVVV",
  machhws_3 =		"100000D8RRR.",
  nmachhws_3 =		"100000dcRRR.",
  vadduqm_3 =		"10000100VVV",
  vmaxsb_3 =		"10000102VVV",
  vslb_3 =		"10000104VVV",
  vmulosb_3 =		"10000108VVV",
  vrefp_2 =		"1000010aV-V",
  vmrglb_3 =		"1000010cVVV",
  vpkshus_3 =		"1000010eVVV",
  mulchwu_3 =		"10000110RRR.",
  macchwu_3 =		"10000118RRR.",
  vaddcuq_3 =		"10000140VVV",
  vmaxsh_3 =		"10000142VVV",
  vslh_3 =		"10000144VVV",
  vmulosh_3 =		"10000148VVV",
  vrsqrtefp_2 =		"1000014aV-V",
  vmrglh_3 =		"1000014cVVV",
  vpkswus_3 =		"1000014eVVV",
  mulchw_3 =		"10000150RRR.",
  macchw_3 =		"10000158RRR.",
  nmacchw_3 =		"1000015cRRR.",
  vaddcuw_3 =		"10000180VVV",
  vmaxsw_3 =		"10000182VVV",
  vslw_3 =		"10000184VVV",
  vmulosw_3 =		"10000188VVV",
  vexptefp_2 =		"1000018aV-V",
  vmrglw_3 =		"1000018cVVV",
  vpkshss_3 =		"1000018eVVV",
  macchwsu_3 =		"10000198RRR.",
  vmaxsd_3 =		"100001c2VVV",
  vsl_3 =		"100001c4VVV",
  vcmpgefp_3 =		"100001c6VVV", 
  vlogefp_2 =		"100001caV-V",
  vpkswss_3 =		"100001ceVVV",
  macchws_3 =		"100001d8RRR.",
  nmacchws_3 =		"100001dcRRR.",
  vadduhs_3 =		"10000240VVV",
  vminuh_3 =		"10000242VVV",
  vsrh_3 =		"10000244VVV",
  vcmpgtuh_3 =		"10000246VVV",
  vmuleuh_3 =		"10000248VVV",
  vrfiz_2 =		"1000024aV-V",
  vsplth_3 =		"1000024cVVa",
  vupkhsh_2 =		"1000024eV-V",
  vminuw_3 =		"10000282VVV",
  vminud_3 =		"100002c2VVV",
  vcmpgtud_3 =		"100002c7VVV",
  vrfim_2 =		"100002caV-V",
  vcmpgtsb_3 =		"10000306VVV",
  vcfux_3 =		"1000030aVVy",
  vaddshs_3 =		"10000340VVV",
  vminsh_3 =		"10000342VVV",
  vsrah_3 =		"10000344VVV",   
  vcmpgtsh_3 =		"10000346VVV",
  vmulesh_3 =		"10000348VVV",
  vcfsx_3 =		"1000034aVVy",
  vspltish_2 =		"1000034cV}",
  vupkhpx_2 =		"1000034eV-V",
  mullhw_3 =		"10000350RRR.",
  maclhw_3 =		"10000358RRR.",
  nmaclhw_3 =		"1000035cRRR.",
  vaddsws_3 =		"10000380VVV",
  vminsw_3 =		"10000382VVV",
  vsraw_3 =		"10000384VVV",
  vcmpgtsw_3 =		"10000386VVV",
  vmulesw_3 =		"10000388VVV",
  vctuxs_3 =		"1000038aVVy",
  vspltisw_2 =		"1000038cV}",
  maclhwsu_3 =		"10000398RRR.",
  vminsd_3 =		"100003c2VVV",
  vsrad_3 =		"100003c4VVV",
  vcmpbfp_3 =		"100003c6VVV", 
  vcmpgtsd_3 =		"100003c7VVV",
  vctsxs_3 =		"100003caVVy",
  vupklpx_2 =		"100003ceV-V",
  maclhws_3 =		"100003D8RRR.",
  nmaclhws_3 =		"100003dcRRR.",
  vsububm_3 =		"10000400VVV",
  ["bcdadd._4"] =	"10000401VVVN.",
  vavgub_3 =		"10000402VVV",
  vand_3 =		"10000404VVV",
  ["vcmpequb._3"] =	"10000406VVV",
  vmaxfp_3 =		"1000040aVVV",
  machhwuo_3 =		"10000418RRR.",
  vsubuhm_3 =		"10000440VVV",
  ["bcdsub._4"] =	"10000441VVVN.",
  vavguh_3 =		"10000442VVV",
  vandc_3 =		"10000444VVV",
  ["vcmpequh._3"] =	"10000446VVV",
  vminfp_3 =		"1000044aVVV",
  vpkudum_3 =		"1000044eVVV",
  nmachhwo_3 =		"1000045cRRR.",
  vsubuwm_3 =		"10000480VVV",
  vavguw_3 =		"10000482VVV",
  vor_3 =		"10000484VVV",
  ["vcmpequw._3"] =	"10000486VVV",
  vpmsumw_3 =		"10000488VVV",
  machhwsuo_3 =		"10000498RRR.",
  ["vcmpeqfp._3"] =	"100004c6VVV",
  ["vcmpequd._3"] =	"100004c7VVV",
  vpkudus_3 =		"100004ceVVV",
  machhwso_3 =		"100004D8RRR.",
  nmachhwso_3 =		"100004dcRRR.",
  vavgsb_3 =		"10000502VVV",
  macchwuo_3 =		"10000518RRR.",
  vavgsh_3 =		"10000542VVV",
  vorc_3 =		"10000544VVV",
  vbpermq_3 =		"1000054cVVV",
  vpksdus_3 =		"1000054eVVV",
  macchwo_3 =		"10000558RRR.",
  nmacchwo_3 =		"1000055cRRR.",
  vavgsw_3 =		"10000582VVV",
  macchwsuo_3 =		"10000598RRR.",
  vsld_3 =		"100005c4VVV",
  ["vcmpgefp._3"] =	"100005c6VVV",
  vpksdss_3 =		"100005ceVVV",
  macchwso_3 =		"100005d8RRR.",
  nmacchwso_3 =		"100005dcRRR.",
  vsububs_3 =		"10000600VVV",
  mfvscr_1 =		"10000604V--",
  vsum4ubs_3 =		"10000608VVV",
  vsubuhs_3 =		"10000640VVV",
  mtvscr_1 =		"10000644--V",
  ["vcmpgtuh._3"] =	"10000646VVV",
  vsum4shs_3 =		"10000648VVV",
  vupkhsw_2 =		"1000064eV-V",
  vsubuws_3 =		"10000680VVV",          
  vshasigmaw_4 =	"10000682VVsP",
  veqv_3 =		"10000684VVV",
  vsum2sws_3 =		"10000688VVV",
  vmrgow_3 =		"1000068cVVV",
  vshasigmad_4 =	"100006c2VVsP",
  vsrd_3 =		"100006c4VVV",
  ["vcmpgtud._3"] =	"100006c7VVV",
  vupklsw_2 =		"100006ceV-V",
  vupkslw_2 =		"100006ceV-V",
  vsubsbs_3 =		"10000700VVV",
  vclzb_2 =		"10000702V-V",
  vpopcntb_2 =		"10000703V-V",
  ["vcmpgtsb._3"] =	"10000706VVV",
  vsum4sbs_3 =		"10000708VVV",
  vsubshs_3 =		"10000740VVV",
  vclzh_2 =		"10000742V-V",
  vpopcnth_2 =		"10000743V-V",
  ["vcmpgtsh._3"] =	"10000746VVV",
  maclhwo_3 =		"10000758RRR.",
  nmaclhwo_3 =		"1000075cRRR.",
  vsubsws_3 =		"10000780VVV",
  vclzw_2 =		"10000782V-V",
  vpopcntw_2 =		"10000783V-V",
  ["vcmpgtsw._3"] =	"10000786VVV",
  vsumsws_3 =		"10000788VVV",
  vmrgew_3 =		"1000078cVVV",
  maclhwsuo_3 =		"10000798RRR.",
  vclzd_2 =		"100007c2V-V",
  vpopcntd_2 =		"100007c3V-V",
  ["vcmpbfp._3"] =	"100007c6VVV",
  ["vcmpgtsd._3"] =	"100007c7VVV",
  maclhwso_3 =		"100007D8RRR.",
  nmaclhwso_3 =		"100007dcRRR.",

  -- Primary Opcode 17
  sc_1 =		"44000002?",

  -- Primary Opcode 19
  rfid_0 =		"4c000024",
  rfmci_0 =		"4c00004c",
  rfdi_0 =		"4c00004e",
  rfi_0 =		"4c000064",
  rfci_0 =		"4c000066",
  rfgi_0 =		"4c0000cc",
  rfebb_1 =		"4c000124p",
  dnh_2 =		"4c00018cqQ",
  hrfid_0 =		"4c000224",
  doze_0 =		"4c000324",
  nap_0 =		"4c000364",
  sleep_0 =		"4c0003a4",
  rvwinkle_0 =		"4c0003e4",
  bctar_3 =		"4c000460AAr",
  bctarl_3 =		"4c000461AAr",

  -- Primary Opcode 30
  rldicl_4 =		"78000000RR~ou.",
  rldicr_4 =		"78000004RR~ou.", 
  rldic_4 =		"78000008RR~ou.",
  rldimi_4 =		"7800000cRR~o{.",
  rldcl_4 =		"78000010RR~Ru.", 
  rldcr_4 =		"78000012RR~Ru.",

  -- Primary Opcode 31
  lvls_3 =		"7c00000cVRR",
  lvsl_3 =		"7c00000cVRR",
  lxsiwzx_3 =		"7c000018iRR",
  tlbilx_3 =		"7c000024TRR",
  mfocrf_2 =		"7c000026RE",
  icbt_3 =		"7c00002c:PRR",
  ldepx_3 =		"7c00003aRRR",
  lwepx_3 =		"7c00003eRRR",
  lvsr_3 =		"7c00004cVRR",
  mfvsrd_2 =		"7c000066Rn",
  lbarx_4 =		"7c000068RRRL",
  wait_1 =		"7c00007ce",
  dcbstep_2 =		"7c00007e-RR",    
  lvewx_3 =		"7c00008eVRR",  
  addg6s_3 =		"7c000094RRR",
  lxsiwax_3 =		"7c000098iRR",
  dlmzb_3 =		"7c00009cRR~R.",
  mfmsr_1 =		"7c0000a6R--",
  lbepx_3 =		"7c0000beRRR",
  lvx_3 =		"7c0000ceVRR",
  mfvsrwz_2 =		"7c0000e6Rn",
  lharx_4 =		"7c0000e8RRRL",
  dcbfep_2 =		"7c0000fe-RR",         
  wrtee_1 =		"7c000106R--",
  dcbtstls_3 =		"7c00010c:PRR",
  stvebx_3 =		"7c00010eVRR",
  stxsiwx_3 =		"7c000118iRR",
  msgsndp_1 =		"7c00011c--R",
  mtmsr_1 =		"7c000124R--",
  mtsle_1 =		"7c000126k",
  ["stwcx._3"] =	"7c00012dRRR",
  stdepx_3 =		"7c00013aRRR",
  stwepx_3 =		"7c00013eRRR",
  wrteei_1 =		"7c000146--[",
  dcbtls_3 =		"7c00014c:PRR",
  stvehx_3 =		"7c00014eVRR",
  msgclrp_1 =		"7c00015c--R",
  mtmsrd_2 =		"7c000164Rx",
  mtvsrd_2 =		"7c000166iR",
  ["stqcx._3"] =	"7c00016dMRR",
  ["icblq._3"] =		"7c00018d:PRR",
  stvewx_3 =		"7c00018eVRR",
  msgsnd_1 =		"7c00019c--R",
  mtsr_2 =		"7c0001a4ZR~",
  mtvsrwa_2 =		"7c0001a6iR",
  ["stdcx._3"] =	"7c0001adRRR",
  stbepx_3 =		"7c0001beRRR",
  icblc_3 =		"7c0001cc:PRR",
  stvx_3 =		"7c0001ceVRR",
  msgclr_1 =		"7c0001dc--R",
  mtsrin_2 =		"7c0001e4R-R",
  mtvsrwz_2 =		"7c0001e6iR",
  bpermd_3 =		"7c0001f8RR~R",
  dcbtstep_3 =		"7c0001feTRR",
  mfdcrx_2 =		"7c000206RR",
  mfcdrx_2 =		"7c000206RR-",
  lvepxl_3 =		"7c00020eVRR",
  ehpriv_0 =		"7c00021c",
  tlbiel_1 =		"7c000224--R",
  lqarx_4 =		"7c000228MRRL", 
  cdtbcd_2 =		"7c000234RR~",
  lhepx_3 =		"7c00023eRRR",
  mfdcrux_2 =		"7c000246RR-",
  lvepx_3 =		"7c00024eVRR",
  mfbhrbe_2 =		"7c00025cRQ",
  tlbie_2 =		"7c000264--R]",
  cbcdtd_2 =		"7c000274RR~",
  dcbtep_3 =		"7c00027eTRR",
  mfdcr_2 =		"7c000286R*",
  dcread_3 =		"7c00028cRRR",
  lxvdsx_3 =		"7c000298iRR",
  mfpmr_2 =		"7c00029cR*",
  mfspr_2 =		"7c0002a6R*",
  lvxl_3 =		"7c0002ceVRR",
  tlbia_0 =		"7c0002e4",
  popcntw_2 =		"7c0002f4RR~",
  mtdcrx_2 =		"7c000306RR~",
  dcblc_3 =		"7c00030c:PRR.",
  divdeu_3 =		"7c000312RRR.",
  divweu_3 =		"7c000316RRR.",
  slbmte_2 =		"7c000324R-R",
  sthepx_3 =		"7c00033eRRR",
  mtdcrux_2 =		"7c000346RR~",
  ["dcblq._3"] =	"7c00034dZRR",
  divde_3 =		"7c000352RRR.",
  divwe_3 =		"7c000356RRR.", 
  clrbhrb_0 =		"7c00035c",
  slbie_1 =		"7c000364--R",
  mtdcr_2 =		"7c000386VR~",
  dci_1 =		"7c00038c:P", 
  mtpmr_2 =		"7c00039c|R",
  mtspr_2 =		"7c0003a6|R",
  dsn_2 =		"7c0003c6-RR",
  icbtls_3 =		"7c0003cc:PRR",
  stvxl_3 =		"7c0003ceVRR",
  slbia_0 =		"7c0003e4",
  popcntd_2 =		"7c0003f4RR~",
  lbdx_3 =		"7c000406RRR",
  lxsspx_3 =		"7c000418iRR",
  lhdx_3 =		"7c000446RRR",
  tlbsync_0 =		"7c00046c",
  lwdx_3 =		"7c000486RRR",
  lxsdx_3 =		"7C000498iRR",
  mfsr_2 =		"7c0004a6RZ",
  lfdepx_3 =		"7c0004beFRR",
  lddx_3 =		"7c0004c6RRR",
  stbdx_3 =		"7c000506RRR",
  stxsspx_3 =		"7c000518iRR",
  ["tbegin._1"] =	"7c00051dg",
  mfsrin_2 =		"7c000526R-R",
  sthdx_3 =		"7c000546RRR",
  ["tend._0"] =		"7c00055d",
  ["stbcx._3"] =	"7c00056dRRR",
  ["stbcix._3"] =	"7c00056dRRR",
  stwdx_3 =		"7c000586RRR",
  stxsdx_3 =		"7c000598iRR",
  tcheck_1 =		"7c00059cX",
  ["sthcx._3"] =	"7c0005adRRR",
  stfdepx_3 =		"7c0005beFRR",
  stddx_3 =		"7c0005c6RRR",
  ["tsr._1"] =		"7c0005ddk",
  stvepxl_3 =		"7c00060eVRR",
  lxvw4x_3 =		"7c000618iRR",
  ["tabortwc._3"] =	"7c00061dTRR",
  tlbivax_2 =		"7c000624-RR",
  lwzcix_3 =		"7c00062aRRR",
  lfdpx_3 =		"7c00062eHRR",
  lfddx_3 =		"7c000646FRR",
  stvepx_3 =		"7C00064eVRR",
  ["tabortdc._3"] =	"7c00065dTRR",
  lhzcix_3 =		"7c00066aRRR",
  sradi_3 =		"7c000674RR~o.",
  lxvd2x_3 =		"7c000698iRR",
  ["tabortwci._3"] =	"7c00069dTR}",
  ["tlbsrx._2"] =	"7c0006a5-RR",
  slbmfev_2 =		"7c0006a6R-R",
  lbzcix_3 =		"7c0006aaRRR",
  ["tabortdci._3"] =	"7c0006ddTR}",
  ldcix_3 =		"7c0006eaRRR",
  divdeuo_3 =		"7c000712RRR.",
  divweuo_3 =		"7c000716RRR.",
  stxvw4x_3 =		"7c000718iRR",
  ["tabort._1"] =	"7c00071d-R-",
  tlbsx_2 =		"7c000724-RR",
  slbmfee_2 =		"7c000726R-R",
  stwcix_3 =		"7c00072aRRR",      
  stfdpx_3 =		"7c00072eHRR",
  stfddx_3 =		"7c000746FRR",
  divdeo_3 =		"7c000752RRR.",
  divweo_3 =		"7c000756RRR.",
  ["treclaim._1"] =	"7c00075d-R",
  tlbre_0 =		"7c000764",      
  sthcix_3 =		"7c00076aRRR",
  ici_1 =		"7c00078c:P--",
  stxvd2x_3 =		"7c000798iRR",
  tlbwe_0 =		"7c0007a4",
  ["slbfee._2"] =	"7c0007a7R-R",
  stbcix_3 =		"7c0007aaRRR",
  icbiep_2 =		"7c0007be-RR",
  icread_2 =		"7c0007cc-RR",
  ["trechkpt._0"] =	"7c0007dd",
  stdcix_3 =		"7c0007eaRRR",
  dcbzep_2 =		"7c0007FE-RR",  
  mtocrf_2 =		"7c100120/R",

  -- Primary Opcode 56
  lq_2 =		"e0000000Mc",

  -- Primary Opcode 57
  lfdp_2 =		"e4000000HD",

  -- Primary Opcode 59            
  dadd_3 =		"ec000004FFF.",
  dqua_4 =		"ec000006FFFY.",
  dmul_3 =		"ec000044FFF.",
  drrnd_4 =		"ec000046FFFY.",
  dscli_3 =		"ec000084FF{.",
  dquai_4 =		"ec000086fF-FY.",
  dscri_3 =		"ec0000c4FF{.",
  drintx_4 =		"ec0000c6jF-FY.",
  dcmpo_3 =		"ec000104XFF",
  dtstex_3 =		"ec000144XFF",
  dtstdc_3 =		"ec000184XF{",
  dtstdg_3 =		"ec0001c4XF{",
  drintn_4 =		"ec0001c6jF-FY.",
  dctdp_2 =		"ec000204F-F.",
  dctfix_2 =		"ec000244F-F.",
  ddedpd_3 =		"ec000284BF-F.",
  dxex_2 =		"ec0002c4F-F.",
  dsub_3 =		"ec000404FFF.",
  ddiv_3 =		"ec000444FFF.",
  dcmpu_3 =		"ec000504XFF",
  dtstsf_3 =		"ec000544XFF",
  drsp_2 =		"ec000604F-F.",
  dcffix_2 =		"ec000644F-F.",
  denbcd_3 =		"ec000684bF-F.",
  fcfids_2 =		"ec00069cF-F.",
  diex_3 =		"ec0006c4FFF.",
  fcfidus_2 =		"ec00079cF-F.",

  -- Primary Opcode 60
  xsaddsp_3 =		"f0000000@!$",
  xsmaddasp_3 =		"f0000008@!$",
  xxsldwi_4 =		"f0000010@!$l",
  xsrsqrtesp_2 =	"f0000028@-$",
  xssqrtsp_2 =		"f000002c@-$",
  xxsel_4 =		"f0000030@!$&", 
  xssubsp_3 =		"f0000040@!$",
  xsmaddmsp_3 =		"f0000048@!$",
  xxpermdi_4 =		"f0000050@!$l",
  xsresp_2 =		"f0000068@-$", 
  xsmulsp_3 =		"f0000080@!$",
  xsmsubasp_3 =		"f0000088@!$",
  xxmrghw_3 =		"f0000090@!$",
  xsdivsp_3 =		"f00000c0@!$",
  xsmsubmsp_3 =		"f00000c8@!$",
  xsadddp_3 =		"f0000100@!$",
  xsmaddadp_3 =		"f0000108@!$",
  xscmpudp_3 =		"f0000118X!$",
  xscvdpuxws_2 =	"f0000120@-$",
  xsrdpi_2 =		"f0000124@-$",
  xsrsqrtedp_2 =	"f0000128@-$",
  xssqrtdp_2 =		"f000012c@-$",
  xssubdp_3 =		"f0000140@!$",
  xsmaddmdp_3 =		"f0000148@!$",
  xscmpodp_3 =		"f0000158X!$",
  xscvdpsxws_2 =	"f0000160@-$",
  xsrdpiz_2 =		"f0000164@-$",
  xsredp_2 =		"f0000168@-$",
  xsmuldp_3 =		"f0000180@!$",
  xsmsubadp_3 =		"f0000188@!$",
  xxmrglw_3 =		"f0000190@!$",
  xsrdpip_2 =		"f00001a4@-$",
  xstsqrtdp_2 =		"f00001a8X-$",
  xsrdpic_2 =		"f00001ac@-$",
  xsdivdp_3 =		"f00001c0@!$",
  xsmsubmdp_3 =		"f00001c8@!$",
  xsrdpim_2 =		"f00001e4@-$", 
  xstdivdp_3 =		"f00001e8X!$",
  xvaddsp_3 =		"f0000200@!$",
  xvmaddasp_3 =		"f0000208@!$",
  xvcmpeqsp_3 =		"f0000218@!$", 
  xvcvspuxws_2 =	"f0000220@-$",
  xvrspi_2 =		"f0000224@-$",
  xvrsqrtesp_2 =	"f0000228@-$",
  xvsqrtsp_2 =		"f000022c@-$",
  xvsubsp_3 =		"f0000240@!$",
  xvmaddmsp_3 =		"f0000248@!$",
  xvcmpgtsp_3 =		"f0000258@!$",
  xvcvspsxws_2 =	"f0000260@-$",
  xvrspiz_2 =		"f0000264@-$",
  xvresp_2 =		"f0000268@-$",
  xvmulsp_3 =		"f0000280@!$",
  xvmsubasp_3 =		"f0000288@!$",
  xxspltw_3 =		"f0000290@-$(",
  xvcmpgesp_3 =		"f0000298@!$",
  xvcvuxwsp_2 =		"f00002a0@-$",
  xvrspip_2 =		"f00002a4@-$",
  xvtsqrtsp_2 =		"f00002a8X-$",
  xvrspic_2 =		"f00002ac@-$",
  xvdivsp_3 =		"f00002c0@!$",
  xvmsubmsp_3 =		"f00002c8@!$",
  xvcvsxwsp_2 =		"f00002e0@-$",
  xvrspim_2 =		"f00002e4@-$",
  xvtdivsp_3 =		"f00002e8X!$",
  xvadddp_3 =		"f0000300@!$",
  xvmaddadp_3 =		"f0000308@!$",
  xvcmpeqdp_3 =		"f0000318@!$",
  xvcvdpuxws_2 =	"f0000320@-$",
  xvrdpi_2 =		"f0000324@-$",
  xvrsqrtedp_2 =	"f0000328@-$",
  xvsqrtdp_2 =		"f000032c@-$",
  xvsubdp_3 =		"f0000340@!$",
  xvmaddmdp_3 =		"f0000348@!$",
  xvcmpgtdp_3 =		"f0000358@!$",
  xvcvdpsxws_2 =	"f0000360@-$",
  xvrdpiz_2 =		"f0000364@-$",
  xvredp_2 =		"f0000368@-$",
  xvmuldp_3 =		"f0000380@!$",
  xvmsubadp_3 =		"f0000388@!$", 
  xvcmpgedp_3 =		"f0000398@!$",
  xvcvuxwdp_2 =		"f00003a0@-$",
  xvrdpip_2 =		"f00003a4@-$",
  xvtsqrtdp_2 =		"f00003a8X-$",
  xvrdpic_2 =		"f00003ac@-$",
  xvdivdp_3 =		"f00003c0@!$",
  xvmsubmdp_3 =		"f00003c8@!$",
  xvcvsxwdp_2 =		"f00003e0@-$",
  xvrdpim_2 =		"f00003e4@-$",
  xvtdivdp_3 =		"f00003e8X!$",
  xsnmaddasp_3 =	"f0000408@!$",
  xxland_3 =		"f0000410@!$",
  xscvdpsp_2 =		"f0000424@-$",
  xscvdpspn_2 =		"f000042c@-$",
  xsnmaddmsp_3 =	"f0000448@!$",
  xxlandc_3 =		"f0000450@!$",
  xsrsp_2 =		"f0000464@-$",
  xsnmsubasp_3 =	"f0000488@!$",
  xxlor_3 =		"f0000490@!$",
  xscvuxdsp_2 =		"f00004a0@-$",
  xsnmsubmsp_3 =	"f00004c8@!$",
  xxlxor_3 =		"f00004d0@!$",
  xscvsxdsp_2 =		"f00004e0@-$",
  xsmaxdp_3 =		"f0000500@!$",
  xsnmaddadp_3 =	"f0000508@!$",
  xxlnor_3 =		"f0000510@!$",
  xscvdpuxds_2 =	"f0000520@-$",
  xscvspdp_2 =		"f0000524@-$",
  xscvspdpn_2 =		"f000052c@-$",
  xsmindp_3 =		"f0000540@!$",
  xsnmaddmdp_3 =	"f0000548@!$",
  xxlorc_3 =		"f0000550@!$",
  xscvdpsxds_2 =	"f0000560@-$",
  xsabsdp_2 =		"f0000564@-$",
  xscpsgndp_3 =		"f0000580@!$",
  xsnmsubadp_3 =	"f0000588@!$",
  xxlnand_3 =		"f0000590@!$",
  xscvuxddp_2 =		"f00005a0@-$",
  xsnabsdp_2 =		"f00005a4@-$",
  xsnmsubmdp_3 =	"f00005c8@!$",
  xxleqv_3 =		"f00005d0@!$",
  xscvsxddp_2 =		"f00005e0@-$",
  xsnegdp_2 =		"f00005e4@-$",
  xvmaxsp_3 =		"f0000600@!$",
  xvnmaddasp_3 =	"f0000608@!$",
  ["xvcmpeqsp._3"] =	"f0000618@!$",
  xvcvspuxds_2 =	"f0000620@-$",
  xvcvdpsp_2 =		"f0000624@-$",
  xvminsp_3 =		"f0000640@!$",
  xvnmaddmsp_3 =	"f0000648@!$",
  ["xvcmpgtsp._3"] =	"f0000658@!$",
  xvcvspsxds_2 =	"f0000660@-$",
  xvabssp_2 =		"f0000664@-$",
  xvcpsgnsp_3 =		"f0000680@!$",
  xvnmsubasp_3 =	"f0000688@!$",
  ["xvcmpgesp._3"] =	"f0000698@!$",
  xvcvuxdsp_2 =		"f00006a0@-$",
  xvnabssp_2 =		"f00006a4@-$",
  xvnmsubmsp_3 =	"f00006c8@!$",
  xvcvsxdsp_2 =		"f00006e0@-$",
  xvnegsp_2 =		"f00006e4@-$",
  xvmaxdp_3 =		"f0000700@!$",
  xvnmaddadp_3 =	"f0000708@!$",
  ["xvcmpeqdp._3"] =	"f0000718@!$",
  xvcvdpuxds_2 =	"f0000720@-$",
  xvcvspdp_2 =		"f0000724@-$",
  xvmindp_3 =		"f0000740@!$",
  xvnmaddmdp_3 =	"f0000748@!$",
  ["xvcmpgtdp._3"] =	"f0000758@!$",
  xvcvdpsxds_2 =	"f0000760@-$",
  xvabsdp_2 =		"f0000764@-$",
  xvcpsgndp_3 =		"f0000780@!$",
  xvnmsubadp_3 =	"f0000788@!$",
  ["xvcmpgedp._3"] =	"f0000798@!$",
  xvcvuxddp_2 =		"f00007a0@-$",
  xvnabsdp_2 =		"f00007a4@-$",
  xvnmsubmdp_3 =	"f00007c8@!$",
  xvcvsxddp_2 =		"f00007e0@-$",
  xvnegdp_2 =		"f00007e4@-$",

  -- Primary Opcode 61  
  stfdp_2 =		"f4000000HD",

  -- Primary Opcode 62
  stq_2 =		"F8000002M<",

  -- Primary Opcode 63
  daddq_3 =		"fc000004HHH.",
  dquaq_4 =		"fc000006HHHY.",
  dmulq_3 =		"fc000044HHH.",
  drrndq_4 =		"fc000046HHHY.",
  dscliq_3 =		"fc000084HH{.",
  dquaiq_4 =		"fc000086fH-HY.",
  dscriq_3 =		"fc0000c4HH{.",
  drintxq_4 =		"fc0000c6jH-HY.",
  ftdiv_3 =		"fc000100XFF",
  dcmpoq_3 =		"fc000104XHH",
  fctiwu_2 =		"fc00011cF-F.",
  fctiwuz_2 =		"fc00011eF-F.",
  ftsqrt_2 =		"fc000140X-F",
  dtstexq_3 =		"fc000144XHH",
  dtstdcq_3 =		"fc000184XH{",
  dtstdgq_3 =		"fc0001c4XH{",
  drintnq_4 =		"fc0001c6jH-HY.",
  dctqpq_2 =		"fc000204H-H.",
  dctfixq_2 =		"fc000244H-H.",
  ddedpdq_3 =		"fc000284BH-H.",
  dxexq_2 =		"fc0002c4H-H.",
  dsubq_3 =		"fc000404HHH.",
  ddivq_3 =		"fc000444HHH.",
  dcmpuq_3 =		"fc000504XHH",
  dtstsfq_3 =		"fc000544XHH",
  mtfsf_4 =		"fc00058ezFwx.",
  drdpq_2 =		"fc000604H-H.",
  dcffixq_2 =		"fc000644H-H.",
  denbcdq_3 =		"fc000684bH-H.",
  fmrgow_3 =		"fc00068cFFF",
  diexq_3 =		"fc0006c4HHH.",
  fctidu_2 =		"fc00075cF-F.",
  fctiduz_2 =		"fc00075eF-F.",
  fmrgew_3 =		"fc00078cFFF",
}

-- Add mnemonics for "." variants.
do
  local t = {}
  for k,v in pairs(map_op) do
    if sub(v, -1) == "." then
      local v2 = sub(v, 1, 7)..char(byte(v, 8)+1)..sub(v, 9, -2)
      t[sub(k, 1, -3).."."..sub(k, -2)] = v2
    end
  end
  for k,v in pairs(t) do
    map_op[k] = v
  end
end

-- Add more branch mnemonics.
for cond,c in pairs(map_cond) do
  local b1 = "b"..cond
  local c1 = (c%4)*0x00010000 + (c < 4 and 0x01000000 or 0)
  -- bX[l]
  map_op[b1.."_1"] = tohex(0x40800000 + c1).."K"
  map_op[b1.."y_1"] = tohex(0x40a00000 + c1).."K"
  map_op[b1.."l_1"] = tohex(0x40800001 + c1).."K"
  map_op[b1.."_2"] = tohex(0x40800000 + c1).."-XK"
  map_op[b1.."y_2"] = tohex(0x40a00000 + c1).."-XK"
  map_op[b1.."l_2"] = tohex(0x40800001 + c1).."-XK"
  -- bXlr[l]
  map_op[b1.."lr_0"] = tohex(0x4c800020 + c1)
  map_op[b1.."lrl_0"] = tohex(0x4c800021 + c1)
  map_op[b1.."ctr_0"] = tohex(0x4c800420 + c1)
  map_op[b1.."ctrl_0"] = tohex(0x4c800421 + c1)
  -- bXctr[l]
  map_op[b1.."lr_1"] = tohex(0x4c800020 + c1).."-X"
  map_op[b1.."lrl_1"] = tohex(0x4c800021 + c1).."-X"
  map_op[b1.."ctr_1"] = tohex(0x4c800420 + c1).."-X"
  map_op[b1.."ctrl_1"] = tohex(0x4c800421 + c1).."-X"
end

-- Parse GPR (Fixed Point Registers) : r[0-31]
-- Pair == 0 : standard mode
-- Pair == 1 : pair mode (even address only)
local function parse_gpr(expr) 
  local tname, ovreg = match(expr, "^([%w_]+):(r[1-3]?[0-9])$")
  local tp = map_type[tname or expr]
  if tp then
    local reg = ovreg or tp.reg
    if not reg then
      werror("type `"..(tname or expr).."' needs a register override")
    end
    expr = reg
  end
  local r = match(expr, "^r([1-3]?[0-9])$")
  if r then
    r = tonumber(r)
    if r <= 31 then
        return r, tp 
    end
  end
  werror("bad register name `"..expr.."'")
end

local function parse_gpr_pair(expr) 
  local tname, ovreg = match(expr, "^([%w_]+):(r[1-3]?[0-9])$")
  local tp = map_type[tname or expr]
  if tp then
    local reg = ovreg or tp.reg
    if not reg then
      werror("type `"..(tname or expr).."' needs a register override")
    end
    expr = reg
  end
  local r = match(expr, "^r([1-3]?[0-9])$")
  if r then
    r = tonumber(r)
    if r <= 31 then
      if r%2 == 0 then
        return r, tp 
      else
        werror("bad register pair (address must be even) `"..expr.."'")
      end
    end
  end
  werror("bad register name `"..expr.."'")
end

-- Parse VR (Vector Registers) : v[0-31]
local function parse_vr(expr)
  local tname, ovreg = match(expr, "^([%w_]+):(v[1-3]?[0-9])$")
  local tp = map_type[tname or expr]
  if tp then
    local reg = ovreg or tp.reg
    if not reg then
      werror("type `"..(tname or expr).."' needs a register override")
    end
    expr = reg
  end
  local r = match(expr, "^v([1-3]?[0-9])$")
  if r then
    r = tonumber(r)
    if r <= 31 then return r, tp end
  end
  werror("bad vector register name `"..expr.."'")
end

-- Parse VS (Vector Scalar Registers) : vs[0-63]
local function parse_vs(expr, mode)
  if mode == nil then mode = 0 end
  local r = match(expr, "^vs([1-6]?[0-9])$")
  if r then
    r = tonumber(r)
    if r <= 63 and r >= 0 then
      if mode == function_modes.lsb5 then
        return band(r, 31)
      elseif mode == 0 then
        return r
      elseif mode == function_modes.msb then 
        return shr(band(r, 32), 5)
      end
    end
  end
  werror("bad vector-scalar extension name `"..expr.."'")
end

-- Parse Floating Point Registers : f[0-31]
local function parse_fpr(expr)
  local r = match(expr, "^f([1-3]?[0-9])$")
  if r then
    r = tonumber(r)
    if r <= 31 then 
      return r 
    end
  end
  werror("bad register name `"..expr.."'")
end

-- Parse Floating Point Registers Pairs : f[0-31] (even)
local function parse_fpr_pair(expr)
  local r = match(expr, "^f([1-3]?[0-9])$")
  if r then
    r = tonumber(r)
    if r <= 31 then 
      if r%2 == 0 then
        return r 
      else
        werror ("bad register pair (address must be even) `"..expr.."'")
      end
    end
  end
  werror("bad register name `"..expr.."'")
end

-- Parses CR Fields
local function parse_cr(expr)
  local r = match(expr, "^cr([0-7])$")
  if r then return tonumber(r) end
  werror("bad condition register name `"..expr.."'")
end

-- Parse Conditionals
local function parse_cond(expr)
  local r, cond = match(expr, "^4%*cr([0-7])%+(%w%w)$")
  if r then
    r = tonumber(r)
    local c = map_cond[cond]
    if c and c < 4 then return r*4+c end
  end
  werror("bad condition bit name `"..expr.."'")
end

local function parse_imm(imm, bits, shift, scale, signed)
  local n = tonumber(imm)
  if n then
    local m = sar(n, scale)
    if shl(m, scale) == n then
      if signed then
	local s = sar(m, bits-1)
	if s == 0 then return shl(m, shift)
	elseif s == -1 then return shl(m + shl(1, bits), shift) end
      else
 if sar(m, bits) == 0 then return shl(m, shift) end
      end
    end
    werror("out of range immediate `"..imm.."'")
  elseif match(imm, "^r([1-3]?[0-9])$") or
         match(imm, "^([%w_]+):(r[1-3]?[0-9])$") or 
         match(imm, "^f([1-3]?[0-9])$") or
         match(imm, "^([%w_]+):(f[1-3]?[0-9])$") or 
         match(imm, "^v([1-3]?[0-9])$") or
         match(imm, "^([%w_]+):(v[1-3]?[0-9])$") or
         match(imm, "^vs([1-3]?[0-9])$") or
         match(imm, "^([%w_]+):(vs[1-3]?[0-9])$") then
    werror("expected immediate operand, got register")
  else
    waction("IMM", (signed and 32768 or 0)+scale*1024+bits*32+shift, imm)
    return 0
  end
end

-- Identify and split 10 bit field, depending o type
local function parse_10bit_field(expr, type)
  if type == nil then type = 0 end
  local r = parse_imm(expr, 10, 0, 0, false)
  if r then
  if r <= 1023 and r >= 0 then
    if type == 0 then
      return r 
    else
      return bor(shl(band(r, 31), 5), shr(band(r, 992), 5));
    end 
  end
  werror("out of range immediate `"..expr.."'")
  end
  werror("Invalid immediate Â´`"..expr.."'")
end

-- Parse Displacements
local function parse_disp(disp)
  local imm, reg = match(disp, "^(.*)%(([%w_:]+)%)$")
  if imm then
    local r = parse_gpr(reg)
  if r == 0 then werror("cannot use r0 in displacement") end
    return r*65536 + parse_imm(imm, 16, 0, 0, true)
  end
  local reg, tailr = match(disp, "^([%w_:]+)%s*(.*)$")
  if reg and tailr ~= "" then
    local r, tp = parse_gpr(reg)
    if r == 0 then werror("cannot use r0 in displacement") end
    if tp then
      waction("IMM", 32768+16*32, format(tp.ctypefmt, tailr))
      return r*65536
    end
  end
  werror("bad displacement `"..disp.."'")
end

-- Parse U Displacement
local function parse_udisp(disp, scale, size)
  local imm, reg = match(disp, "^(.*)%(([%w_:]+)%)$")
  if size == nil then size = 5 end
  if imm then
    local r = parse_gpr(reg)
    if r == 0 then werror("cannot use r0 in displacement") end
    if size == 5 then  return r*65536 + parse_imm(imm, 5, 11, scale, false) 
    elseif size == 12 then return r*65536 + parse_imm(imm, 12, 0, scale, true);
    elseif size == 14 then return r*65536 + parse_imm(imm, 14, 0, scale, true); end
  end
  local reg, tailr = match(disp, "^([%w_:]+)%s*(.*)$")
  if reg and tailr ~= "" then
    local r, tp = parse_gpr(reg)
    if r == 0 then werror("cannot use r0 in displacement") end
    if tp then
      waction("IMM", scale*1024+5*32+11, format(tp.ctypefmt, tailr))
      return r*65536
    end
  end
  werror("bad displacement `"..disp.."'")
end

-- Parse Labels
local function parse_label(label, def)
  local prefix = sub(label, 1, 2)
  -- =>label (pc label reference)
  if prefix == "=>" then
    return "PC", 0, sub(label, 3)
  end
  -- ->name (global label reference)
  if prefix == "->" then
    return "LG", map_global[sub(label, 3)]
  end
  if def then
    -- [1-9] (local label definition)
    if match(label, "^[1-9]$") then
      return "LG", 10+tonumber(label)
    end
  else
    -- [<>][1-9] (local label reference)
    local dir, lnum = match(label, "^([<>])([1-9])$")
    if dir then -- Fwd: 1-9, Bkwd: 11-19.
      return "LG", lnum + (dir == ">" and 0 or 10)
    end
    -- extern label (extern label reference)
    local extname = match(label, "^extern%s+(%S+)$")
    if extname then
      return "EXT", map_extern[extname]
    end
  end
  werror("bad label `"..label.."'")
end

-- Handle opcodes defined with template strings.
map_op[".template__"] = function(params, template, nparams)
  if not params then return sub(template, 9) end
  local op = tonumber(sub(template, 1, 8), 16)
  local n, rs = 1, 26
  
  -- Limit number of section buffer positions used bmakey a single dasm_put().
  -- A single opcode needs a maximum of 3 positions (rlwinm).
  if secpos+3 > maxsecpos then wflush() end
  local pos = wpos()

  -- Process each character.
  for p in gmatch(sub(template, 9), ".") do
    if p == "R" then
      rs = rs - 5; op = op + parse_gpr(params[n]) * 2^rs; n = n + 1;
    elseif p == "V" then
      rs = rs - 5;  op = op + parse_vr(params[n]) * 2^rs; n = n + 1;
    elseif p == "F" then
      rs = rs - 5; op = op + parse_fpr(params[n]) * 2^rs; n = n + 1;
    elseif p == "v" then
      rs = rs - 5; op = op + parse_imm(params[n], 6, rs, 0, false); n = n + 1;
    elseif p == "o" then
      local value = parse_imm(params[n], 6, 0, 0, false)
      local bit_value = shr(value, 5)
      value = band(value, 31) rs = rs - 5; 
      op = op + value * 2^rs; op = bor(shl(bit_value, 1), op); n = n + 1;
    elseif p == "?" then
      local value = parse_imm(params[n], 7, 0, 0, false); op = bor(shl(value, 5), op); n = n + 1;
    elseif p == "i" then
      rs = rs - 5; 
      op = op + parse_vs(params[n], function_modes.lsb5) * 2^rs + parse_vs(params[n], function_modes.msb); 
      n = n + 1;
    elseif p == "n" then
      local first_register = shr(band(op, 65011712), 21);
      op = band(op, -65011713); 
      op = op + parse_vs(params[n], function_modes.lsb5) * 2^rs + parse_vs(params[n], function_modes.msb); 
      rs = rs - 5; op = op + first_register * 2^rs; 
      n = n + 1;
    elseif p == "L" then 
      op = op + parse_imm(params[n], 1, 0, 0, false); n = n + 1;
    elseif p == "M" then
      rs = rs - 5; op = op + parse_gpr_pair(params[n]) * 2^rs; n = n + 1;
    elseif p == "H" then
      rs = rs - 5; op = op + parse_fpr_pair(params[n]) * 2^rs; n = n + 1;
    elseif p == "Z" then
      rs = rs - 5; op = op + parse_imm(params[n], 4, rs, 0, false); n = n + 1;
    elseif p == "k" then
      op = bor(shl(parse_imm(params[n], 1, 0, 0, false), 21), op); 
      rs = rs - 1; n = n + 1;
    elseif p == "p" then
      op = bor(shl(parse_imm(params[n], 1, 0, 0, false), 11), op); 
      rs = rs - 1; n = n + 1;
    elseif p == "m" then
      op = bor(shl(parse_imm(params[n], 3, 0, 0, false), 21), op); 
      n = n + 1;
    elseif p == "N" then
      op = bor(shl(1, 10), op); 
      op = bor(shl(parse_imm(params[n], 1, 0, 0, false), 9), op); 
      n = n + 1;
    elseif p == "A" then
      rs = rs - 5; op = op + parse_imm(params[n], 5, rs, 0, false); n = n + 1;
    elseif p == "}" then
      rs = rs - 5; op = op + parse_imm(params[n], 5, rs, 0, true); n = n + 1;
    elseif p == "h" then
      rs = rs - 5; op = op + parse_imm(params[n], 2, rs, 0, false); n = n + 1;
    elseif p == "S" then
      rs = rs - 5; op = op + parse_imm(params[n], 5, rs, 0, true); n = n + 1;
    elseif p == "I" then
      op = op + parse_imm(params[n], 16, 0, 0, true); n = n + 1;
    elseif p == "U" then
      op = op + parse_imm(params[n], 16, 0, 0, false); n = n + 1;
    elseif p == "D" then
      op = op + parse_disp(params[n]); n = n + 1;
    elseif p == "2" then
      op = op + parse_udisp(params[n], 1); n = n + 1;
    elseif p == "4" then
      op = op + parse_udisp(params[n], 2); n = n + 1;
    elseif p == "8" then
      op = op + parse_udisp(params[n], 3); n = n + 1;
    elseif p == "c" then
      op = op + parse_udisp(params[n], 0, 12); n = n + 1;
    elseif p == "<" then 
      op = op + parse_udisp(params[n], 0, 14); n = n + 1;
    elseif p == "C" then
      rs = rs - 5; op = op + parse_cond(params[n]) * 2^rs; n = n + 1;
    elseif p == "X" then
      rs = rs - 5; op = op + parse_cr(params[n]) * 2^(rs + 2); n = n + 1;
    elseif p == "W" then
      op = op + parse_cr(params[n]); n = n + 1;
    elseif p == "B" then
      op = bor(shl(parse_imm(params[n], 2, 0, 0, false), 19), op); n = n + 1;
    elseif p == "t" then
      op = bor(shl(parse_imm(params[n], 5, 0, 0, false), 16), op); n = n + 1;
    elseif p == "f" then
      op = bor(shl(parse_imm(params[n], 5, 0, 0, true), 16), op); n = n + 1;
    elseif p == "z" then
      op = bor(shl(parse_imm(params[n], 8, 0, 0, false), 17), op); rs = rs - 10; n = n + 1;
    elseif p == "w" then
      op = bor(shl(parse_imm(params[n], 1, 0, 0, false), 25), op); n = n + 1;
    elseif p == "@" then
      local vs_value = parse_vs(params[n]);
      local msb = shr(band(vs_value, 32), 5);
      vs_value = band(vs_value, 31);
      rs = rs - 5; op = op + vs_value * 2^rs + msb; n = n + 1;
    elseif p == "!" then
      local vs_value = parse_vs(params[n]);
      local msb = shr(band(vs_value, 32), 5);
      vs_value = band(vs_value, 31);
      rs = rs - 5; op = op + vs_value * 2^rs + msb * 4; n = n + 1;
    elseif p == "$" then
      local vs_value = parse_vs(params[n]);
      local msb = shr(band(vs_value, 32), 5);
      vs_value = band(vs_value, 31);
      rs = rs - 5; op = op + vs_value * 2^rs + msb * 2; n = n + 1;
    elseif p == "&" then
      local vs_value = parse_vs(params[n]);
      local msb = shr(band(vs_value, 32), 5);
      vs_value = band(vs_value, 31);
      rs = rs - 5; op = op + vs_value * 2^rs + msb * 8; n = n + 1;
    elseif p == "l" then
      rs = rs - 3; op = op + parse_imm(params[n], 2, rs, 0, false); n = n + 1;
    elseif p == "x" then
      op = bor(shl(parse_imm(params[n], 1, 0, 0, false), 16), op); n = n + 1;
    elseif p == "b" then
      op = bor(shl(parse_imm(params[n], 1, 0, 0, false), 20), op); n = n + 1;
    elseif p == "j" then
      op = bor(shl(parse_imm(params[n], 1, 0, 0, false), 16), op); n = n + 1;
    elseif p == "G" then
      op = op + parse_imm(params[n], 8, 12, 0, false); n = n + 1;
    elseif p == "P" then
      rs = rs - 4; op = op + parse_imm(params[n], 4, rs, 0, false); n = n + 1;
    elseif p == "T" then
      rs = rs - 5; op = op + parse_imm(params[n], 5, rs, 0, false); n = n + 1;
    elseif p == "q" then
      rs = rs - 5; op = op + parse_imm(params[n], 5, rs, 0, false); n = n + 1;
    elseif p == "y" then
      local vb_value = shr(band(op, 2031616), 16);
      op = band(op, 4292935679);
      op = op + parse_imm(params[n], 5, 0, 0, false) * 2^rs;  
      op = bor(shl(vb_value, 11), op); n = n + 1;
    elseif p == "a" then
      local vb_value = shr(band(op, 2031616), 16);
      op = band(op, 4292935679);
      op = op + parse_imm(params[n], 3, 0, 0, false) * 2^rs;  
      op = bor(shl(vb_value, 11), op); n = n + 1;
    elseif p == "Q" then
      rs = rs - 10; op = op + parse_10bit_field(params[n]) * 2^rs; n = n + 1;
    elseif p == "*" then
      rs = rs - 10; op = op + parse_10bit_field(params[n], function_modes.split_10bit) * 2^rs; n = n + 1;
    elseif p == "s" then
      rs = rs - 1;  op = op + parse_imm(params[n], 1, rs, 0, false);  n = n + 1;
    elseif p == "e" then
      rs = rs - 5; op = op + parse_imm(params[n], 2, rs, 0, false); n = n + 1;
    elseif p == "g" then
      rs = rs - 5; op = op + parse_imm(params[n], 1, rs, 0, false); n = n + 1;
    elseif p == "]" then
      op = bor(shl(parse_imm(params[n], 1, 0, 0, false), 21), op); n = n + 1;
    elseif p == "[" then
      op = bor(shl(parse_imm(params[n], 1, 0, 0, false), 15), op); n = n + 1;
    elseif p == "Y" then 
      rs = rs - 2; op = op + parse_imm(params[n], 2, rs, 0, false); n = n + 1;
    elseif p == "(" then
      op = bor(shl(parse_imm(params[n], 2, 0, 0, false), 16), op); n = n + 1;
    elseif p == "r" then
      rs = rs - 5; op = op + parse_imm(params[n], 2, rs, 0, false); n = n + 1;
    elseif p == "O" then
      rs = rs - 15; op = op + parse_imm(params[n], 15, rs, 0, false); n = n + 1;
    elseif p == "E" then
      rs = rs - 1; op = op + 1 * 2^rs; rs = rs - 8; 
      op = op + parse_imm(params[n], 8, rs, 0, false); n = n + 1;
    elseif p == "/" then
      local value = parse_imm(params[n], 8, 0, 0, false); op = bor(op, shl(value, 12)); n = n + 1;
    elseif p == "|" then
      local value = parse_10bit_field(params[n], function_modes.split_10bit); op = bor(op, shl(value, 11)); n = n + 1;
    elseif p == "u" then
      rs = rs - 5; op = op + parse_imm(params[n], 6, rs, 0, false); n = n + 1;
    elseif p == "{" then
     rs = rs - 6; op = op + parse_imm(params[n], 6, rs, 0, false); n = n + 1;
    elseif p == "d" then
      op = bor(shl(parse_imm(params[n], 2, 0, 0, false), 16), op); n = n + 1
    elseif p == "J" or p == "K" then
      local mode, n, s = parse_label(params[n], false)
      if p == "K" then n = n + 2048 end
      waction("REL_"..mode, n, s, 1)
      n = n + 1
    elseif p == "0" then
      local mm = 2^rs
      local t = op % mm
      if ((op - t) / mm) % 32 == 0 then werror("cannot use r0") end
    elseif p == "=" or p == "%" then
      local mm = 2^(rs + (p == "%" and 5 or 0))
      local t = ((op - op % mm) / mm) % 32
      rs = rs - 5
      op = op + t * 2^rs
    elseif p == "~" then
      local mm = 2^rs
      local t1l = op % mm
      local t1h = (op - t1l) / mm
      local t2l = t1h % 32
      local t2h = (t1h - t2l) / 32
      local t3l = t2h % 32
      op = ((t2h - t3l + t2l)*32 + t3l)*mm + t1l
    elseif p == "-" then
      rs = rs - 5
    elseif p == ":" then
      rs = rs - 1
    elseif p == "." then
      -- Ignored.
    elseif p == "," then
       local vb_value = band(op, 1024);
       n = n + 1;
    else
      assert(false)
    end
  end
  wputpos(pos, op)
end

------------------------------------------------------------------------------

-- Pseudo-opcode to mark the position where the action list is to be emitted.
map_op[".actionlist_1"] = function(params)
  if not params then return "cvar" end
  local name = params[1] -- No syntax check. You get to keep the pieces.
  wline(function(out) writeactions(out, name) end)
end

-- Pseudo-opcode to mark the position where the global enum is to be emitted.
map_op[".globals_1"] = function(params)
  if not params then return "prefix" end
  local prefix = params[1] -- No syntax check. You get to keep the pieces.
  wline(function(out) writeglobals(out, prefix) end)
end

-- Pseudo-opcode to mark the position where the global names are to be emitted.
map_op[".globalnames_1"] = function(params)
  if not params then return "cvar" end
  local name = params[1] -- No syntax check. You get to keep the pieces.
  wline(function(out) writeglobalnames(out, name) end)
end

-- Pseudo-opcode to mark the position where the extern names are to be emitted.
map_op[".externnames_1"] = function(params)
  if not params then return "cvar" end
  local name = params[1] -- No syntax check. You get to keep the pieces.
  wline(function(out) writeexternnames(out, name) end)
end

------------------------------------------------------------------------------

-- Label pseudo-opcode (converted from trailing colon form).
map_op[".label_1"] = function(params)
  if not params then return "[1-9] | ->global | =>pcexpr" end
  if secpos+1 > maxsecpos then wflush() end
  local mode, n, s = parse_label(params[1], true)
  if mode == "EXT" then werror("bad label definition") end
  waction("LABEL_"..mode, n, s, 1)
end

------------------------------------------------------------------------------

-- Pseudo-opcodes for data storage.
map_op[".long_*"] = function(params)
  if not params then return "imm..." end
  for _,p in ipairs(params) do
    local n = tonumber(p)
    if not n then werror("bad immediate `"..p.."'") end
    if n < 0 then n = n + 2^32 end
    wputw(n)
    if secpos+2 > maxsecpos then wflush() end
  end
end

-- Alignment pseudo-opcode.
map_op[".align_1"] = function(params)
  if not params then return "numpow2" end
  if secpos+1 > maxsecpos then wflush() end
  local align = tonumber(params[1])
  if align then
    local x = align
    -- Must be a power of 2 in the range (2 ... 256).
    for i=1,8 do
      x = x / 2
      if x == 1 then
	waction("ALIGN", align-1, nil, 1) -- Action byte is 2**n-1.
	return
      end
    end
  end
  werror("bad alignment")
end

------------------------------------------------------------------------------

-- Pseudo-opcode for (primitive) type definitions (map to C types).
map_op[".type_3"] = function(params, nparams)
  if not params then
    return nparams == 2 and "name, ctype" or "name, ctype, reg"
  end
  local name, ctype, reg = params[1], params[2], params[3]
  if not match(name, "^[%a_][%w_]*$") then
    werror("bad type name `"..name.."'")
  end
  local tp = map_type[name]
  if tp then
    werror("duplicate type `"..name.."'")
  end
  -- Add #type to defines. A bit unclean to put it in map_archdef.
  map_archdef["#"..name] = "sizeof("..ctype..")"
  -- Add new type and emit shortcut define.
  local num = ctypenum + 1
  map_type[name] = {
    ctype = ctype,
    ctypefmt = format("Dt%X(%%s)", num),
    reg = reg,
  }
  wline(format("#define Dt%X(_V) (int)(ptrdiff_t)&(((%s *)0)_V)", num, ctype))
  ctypenum = num
end
map_op[".type_2"] = map_op[".type_3"]

-- Dump type definitions.
local function dumptypes(out, lvl)
  local t = {}
  for name in pairs(map_type) do t[#t+1] = name end
  sort(t)
  out:write("Type definitions:\n")
  for _,name in ipairs(t) do
    local tp = map_type[name]
    local reg = tp.reg or ""
    out:write(format("  %-20s %-20s %s\n", name, tp.ctype, reg))
  end
  out:write("\n")
end

------------------------------------------------------------------------------

-- Set the current section.
function _M.section(num)
  waction("SECTION", num)
  wflush(true) -- SECTION is a terminal action.
end

------------------------------------------------------------------------------

-- Dump architecture description.
function _M.dumparch(out)
  out:write(format("DynASM %s version %s, released %s\n\n",
    _info.arch, _info.version, _info.release))
  dumpactions(out)
end

-- Dump all user defined elements.
function _M.dumpdef(out, lvl)
  dumptypes(out, lvl)
  dumpglobals(out, lvl)
  dumpexterns(out, lvl)
end

------------------------------------------------------------------------------

-- Pass callbacks from/to the DynASM core.
function _M.passcb(wl, we, wf, ww)
  wline, werror, wfatal, wwarn = wl, we, wf, ww
  return wflush
end

-- Setup the arch-specific module.
function _M.setup(arch, opt)
  g_arch, g_opt = arch, opt
end

-- Merge the core maps and the arch-specific maps.
function _M.mergemaps(map_coreop, map_def)
  setmetatable(map_op, { __index = map_coreop })
  setmetatable(map_def, { __index = map_archdef })
  return map_op, map_def
end

return _M

------------------------------------------------------------------------------
