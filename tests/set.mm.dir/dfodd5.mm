include "codd.mm"
include "cv.mm"
include "c2.mm"
include "cmo.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cz.mm"
include "crab.mm"
include "cc0.mm"
include "wne.mm"
include "dfodd4.mm"
include "wcel.mm"
include "cpr.mm"
include "wb.mm"
include "elmod2.mm"
include "prcom.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "ax-1ne0.mm"
include "elprneb.mm"
include "sylancl.mm"
include "syl.mm"
include "rabbiia.mm"
include "eqtri.mm"

theorem dfodd5
  let vz: setvar z
  let vk: setvar k
  let vx: setvar x


  assert |- Odd = { z e. ZZ | ( z mod 2 ) =/= 0 }

  proof
    codd
    vz
    cv
    #
    c2
    cmo
    co
    #
    c1
    wceq
    #
    vz
    cz
    crab
    @1
    cc0
    wne
    #
    vz
    cz
    crab
    vz
    dfodd4
    @2
    @3
    vz
    cz
    @0
    cz
    wcel
    @1
    cc0
    c1
    cpr
    #
    wcel
    #
    @2
    @3
    wb
    #
    @0
    elmod2
    @5
    @1
    c1
    cc0
    cpr
    #
    wcel
    #
    c1
    cc0
    wne
    @6
    @5
    @8
    @4
    @7
    @1
    cc0
    c1
    prcom
    eleq2i
    biimpi
    ax-1ne0
    @1
    c1
    cc0
    elprneb
    sylancl
    syl
    rabbiia
    eqtri
end
