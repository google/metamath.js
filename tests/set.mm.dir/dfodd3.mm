include "codd.mm"
include "cv.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "crab.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "dfodd6.mm"
include "wcel.mm"
include "wb.mm"
include "wa.mm"
include "eqcom.mm"
include "a1i.mm"
include "rexbidva.mm"
include "odd2np1.mm"
include "bitr4d.mm"
include "rabbiia.mm"
include "eqtri.mm"

theorem dfodd3
  let vz: setvar z
  let vi: setvar i
  let vk: setvar k
  let vx: setvar x


  assert |- Odd = { z e. ZZ | -. 2 || z }

  proof
    codd
    vz
    cv
    #
    c2
    vi
    cv
    #
    cmul
    co
    c1
    caddc
    co
    #
    wceq
    #
    vi
    cz
    wrex
    #
    vz
    cz
    crab
    c2
    @0
    cdvds
    wbr
    wn
    #
    vz
    cz
    crab
    vz
    vi
    dfodd6
    @4
    @5
    vz
    cz
    @0
    cz
    wcel
    #
    @4
    @2
    @0
    wceq
    #
    vi
    cz
    wrex
    @5
    @6
    @3
    @7
    vi
    cz
    @3
    @7
    wb
    @6
    @1
    cz
    wcel
    wa
    @0
    @2
    eqcom
    a1i
    rexbidva
    vi
    @0
    odd2np1
    bitr4d
    rabbiia
    eqtri
end
