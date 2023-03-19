include "ceven.mm"
include "cv.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "crab.mm"
include "cdvds.mm"
include "wbr.mm"
include "dfeven4.mm"
include "wcel.mm"
include "wa.mm"
include "eqcom.mm"
include "2cnd.mm"
include "cc.mm"
include "zcn.mm"
include "adantl.mm"
include "mulcomd.mm"
include "eqeq1d.mm"
include "syl5bb.mm"
include "rexbidva.mm"
include "wb.mm"
include "2z.mm"
include "divides.mm"
include "mpan.mm"
include "bitr4d.mm"
include "rabbiia.mm"
include "eqtri.mm"

theorem dfeven2
  let vz: setvar z
  let vi: setvar i
  let vk: setvar k
  let vx: setvar x


  assert |- Even = { z e. ZZ | 2 || z }

  proof
    ceven
    vz
    cv
    #
    c2
    vi
    cv
    #
    cmul
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
    #
    vz
    cz
    crab
    vz
    vi
    dfeven4
    @4
    @5
    vz
    cz
    @0
    cz
    wcel
    #
    @4
    @1
    c2
    cmul
    co
    #
    @0
    wceq
    #
    vi
    cz
    wrex
    #
    @5
    @6
    @3
    @8
    vi
    cz
    @3
    @2
    @0
    wceq
    @6
    @1
    cz
    wcel
    #
    wa
    #
    @8
    @0
    @2
    eqcom
    @11
    @2
    @7
    @0
    @11
    c2
    @1
    @11
    2cnd
    @10
    @1
    cc
    wcel
    @6
    @1
    zcn
    adantl
    mulcomd
    eqeq1d
    syl5bb
    rexbidva
    c2
    cz
    wcel
    @6
    @5
    @9
    wb
    2z
    vi
    c2
    @0
    divides
    mpan
    bitr4d
    rabbiia
    eqtri
end
