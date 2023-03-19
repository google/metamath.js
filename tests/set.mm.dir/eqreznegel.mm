include "cz.mm"
include "wss.mm"
include "cv.mm"
include "cneg.mm"
include "wcel.mm"
include "cr.mm"
include "crab.mm"
include "wa.mm"
include "wi.mm"
include "ssel.mm"
include "cc.mm"
include "recn.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "negid.mm"
include "0z.mm"
include "syl6eqel.mm"
include "pm4.71i.mm"
include "zrevaddcl.mm"
include "syl5bb.mm"
include "syl5ib.mm"
include "syl6.mm"
include "com23.mm"
include "impd.mm"
include "simpr.mm"
include "a1i.mm"
include "jcad.mm"
include "zre.mm"
include "anim1i.mm"
include "impbid1.mm"
include "weq.mm"
include "negeq.mm"
include "eleq1d.mm"
include "elrab.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem eqreznegel
  let vz: setvar z
  let cA: class A
  let vw: setvar w

  disjoint A z
  disjoint A w
  disjoint w z
  assert |- ( A C_ ZZ -> { z e. RR | -u z e. A } = { z e. ZZ | -u z e. A } )

  proof
    cA
    cz
    wss
    #
    vw
    vz
    cv
    #
    cneg
    #
    cA
    wcel
    #
    vz
    cr
    crab
    #
    @3
    vz
    cz
    crab
    #
    @0
    vw
    cv
    #
    cr
    wcel
    #
    @6
    cneg
    #
    cA
    wcel
    #
    wa
    #
    @6
    cz
    wcel
    #
    @9
    wa
    #
    @6
    @4
    wcel
    @6
    @5
    wcel
    @0
    @10
    @12
    @0
    @10
    @11
    @9
    @0
    @7
    @9
    @11
    @0
    @9
    @7
    @11
    @0
    @9
    @8
    cz
    wcel
    #
    @7
    @11
    wi
    cA
    cz
    @8
    ssel
    @7
    @6
    cc
    wcel
    #
    @13
    @11
    @6
    recn
    @14
    @14
    @6
    @8
    caddc
    co
    #
    cz
    wcel
    #
    wa
    @13
    @11
    @14
    @16
    @14
    @15
    cc0
    cz
    @6
    negid
    0z
    syl6eqel
    pm4.71i
    @6
    @8
    zrevaddcl
    syl5bb
    syl5ib
    syl6
    com23
    impd
    @10
    @9
    wi
    @0
    @7
    @9
    simpr
    a1i
    jcad
    @11
    @7
    @9
    @6
    zre
    anim1i
    impbid1
    @3
    @9
    vz
    @6
    cr
    vz
    vw
    weq
    @2
    @8
    cA
    @1
    @6
    negeq
    eleq1d
    #
    elrab
    @3
    @9
    vz
    @6
    cz
    @17
    elrab
    3bitr4g
    eqrdv
end
