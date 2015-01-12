------------------------------------------------------------------------------
-- DynASM ppc64 module.
--
-- Copyright (C) 2005-2015 Mike Pall. All rights reserved.
-- See dynasm.lua for full copyright notice.
------------------------------------------------------------------------------
-- This module just sets 64 bit mode for the combined ppc/ppc64 module.
-- All the interesting stuff is there.
------------------------------------------------------------------------------

ppc64 = true -- Using a global is an ugly, but effective solution.
return require("dasm_ppc")
