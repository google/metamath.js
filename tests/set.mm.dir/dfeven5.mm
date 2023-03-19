include "ceven.mm"
include "c2.mm"
include "cv.mm"
include "cgcd.mm"
include "co.mm"
include "wceq.mm"
include "cz.mm"
include "crab.mm"
include "wcel.mm"
include "wa.mm"
include "iseven5.mm"
include "weq.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "bitr4i.mm"
include "eqriv.mm"

theorem dfeven5
  let vz: setvar z
  let vx: setvar x
  let vk: setvar k


  assert |- Even = { z e. ZZ | ( 2 gcd z ) = 2 }

  proof
    vx
    ceven
    c2
    vz
    cv
    #
    cgcd
    co
    #
    c2
    wceq
    #
    vz
    cz
    crab
    #
    vx
    cv
    #
    ceven
    wcel
    @4
    cz
    wcel
    c2
    @4
    cgcd
    co
    #
    c2
    wceq
    #
    wa
    @4
    @3
    wcel
    @4
    iseven5
    @2
    @6
    vz
    @4
    cz
    vz
    vx
    weq
    @1
    @5
    c2
    @0
    @4
    c2
    cgcd
    oveq2
    eqeq1d
    elrab
    bitr4i
    eqriv
end
