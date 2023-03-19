include "cc.mm"
include "wcel.mm"
include "cr.mm"
include "cre.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "ci.mm"
include "cim.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cc0.mm"
include "replim.mm"
include "adantr.mm"
include "reim0.mm"
include "oveq2d.mm"
include "it0e0.mm"
include "syl6eq.mm"
include "adantl.mm"
include "recl.mm"
include "recnd.mm"
include "addid1d.mm"
include "3eqtrrd.mm"
include "simpr.mm"
include "eqeltrrd.mm"
include "impbida.mm"

theorem rereb
  let cA: class A


  assert |- ( A e. CC -> ( A e. RR <-> ( Re ` A ) = A ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cr
    wcel
    #
    cA
    cre
    cfv
    #
    cA
    wceq
    #
    @0
    @1
    wa
    #
    cA
    @2
    ci
    cA
    cim
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    @2
    cc0
    caddc
    co
    #
    @2
    @0
    cA
    @7
    wceq
    @1
    cA
    replim
    adantr
    @4
    @6
    cc0
    @2
    caddc
    @1
    @6
    cc0
    wceq
    @0
    @1
    @6
    ci
    cc0
    cmul
    co
    cc0
    @1
    @5
    cc0
    ci
    cmul
    cA
    reim0
    oveq2d
    it0e0
    syl6eq
    adantl
    oveq2d
    @0
    @8
    @2
    wceq
    @1
    @0
    @2
    @0
    @2
    cA
    recl
    #
    recnd
    addid1d
    adantr
    3eqtrrd
    @0
    @3
    wa
    @2
    cA
    cr
    @0
    @3
    simpr
    @0
    @2
    cr
    wcel
    @3
    @9
    adantr
    eqeltrrd
    impbida
end
