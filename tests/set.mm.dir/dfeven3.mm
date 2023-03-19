include "ceven.mm"
include "cv.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cz.mm"
include "wcel.mm"
include "crab.mm"
include "cmo.mm"
include "cc0.mm"
include "wceq.mm"
include "df-even.mm"
include "cr.mm"
include "crp.mm"
include "wb.mm"
include "zre.mm"
include "2rp.mm"
include "mod0.mm"
include "sylancl.mm"
include "bicomd.mm"
include "rabbiia.mm"
include "eqtri.mm"

theorem dfeven3
  let vz: setvar z
  let vk: setvar k
  let vx: setvar x


  assert |- Even = { z e. ZZ | ( z mod 2 ) = 0 }

  proof
    ceven
    vz
    cv
    #
    c2
    cdiv
    co
    cz
    wcel
    #
    vz
    cz
    crab
    @0
    c2
    cmo
    co
    cc0
    wceq
    #
    vz
    cz
    crab
    vz
    df-even
    @1
    @2
    vz
    cz
    @0
    cz
    wcel
    #
    @2
    @1
    @3
    @0
    cr
    wcel
    c2
    crp
    wcel
    @2
    @1
    wb
    @0
    zre
    2rp
    @0
    c2
    mod0
    sylancl
    bicomd
    rabbiia
    eqtri
end
