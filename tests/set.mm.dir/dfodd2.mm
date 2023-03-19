include "codd.mm"
include "cv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cz.mm"
include "wcel.mm"
include "crab.mm"
include "wa.mm"
include "isodd2.mm"
include "weq.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eleq1d.mm"
include "elrab.mm"
include "bitr4i.mm"
include "eqriv.mm"

theorem dfodd2
  let vz: setvar z
  let vx: setvar x
  let vk: setvar k


  assert |- Odd = { z e. ZZ | ( ( z - 1 ) / 2 ) e. ZZ }

  proof
    vx
    codd
    vz
    cv
    #
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    vz
    cz
    crab
    #
    vx
    cv
    #
    codd
    wcel
    @5
    cz
    wcel
    @5
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    wa
    @5
    @4
    wcel
    @5
    isodd2
    @3
    @8
    vz
    @5
    cz
    vz
    vx
    weq
    #
    @2
    @7
    cz
    @9
    @1
    @6
    c2
    cdiv
    @0
    @5
    c1
    cmin
    oveq1
    oveq1d
    eleq1d
    elrab
    bitr4i
    eqriv
end
