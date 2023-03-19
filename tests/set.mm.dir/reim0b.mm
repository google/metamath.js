include "cc.mm"
include "wcel.mm"
include "cr.mm"
include "cim.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "reim0.mm"
include "wa.mm"
include "cre.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "replim.mm"
include "adantr.mm"
include "oveq2.mm"
include "it0e0.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "recl.mm"
include "recnd.mm"
include "addid1d.mm"
include "sylan9eqr.mm"
include "eqtrd.mm"
include "eqeltrd.mm"
include "ex.mm"
include "impbid2.mm"

theorem reim0b
  let cA: class A


  assert |- ( A e. CC -> ( A e. RR <-> ( Im ` A ) = 0 ) )

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
    cim
    cfv
    #
    cc0
    wceq
    #
    cA
    reim0
    @0
    @3
    @1
    @0
    @3
    wa
    #
    cA
    cA
    cre
    cfv
    #
    cr
    @4
    cA
    @5
    ci
    @2
    cmul
    co
    #
    caddc
    co
    #
    @5
    @0
    cA
    @7
    wceq
    @3
    cA
    replim
    adantr
    @3
    @0
    @7
    @5
    cc0
    caddc
    co
    @5
    @3
    @6
    cc0
    @5
    caddc
    @3
    @6
    ci
    cc0
    cmul
    co
    cc0
    @2
    cc0
    ci
    cmul
    oveq2
    it0e0
    syl6eq
    oveq2d
    @0
    @5
    @0
    @5
    cA
    recl
    #
    recnd
    addid1d
    sylan9eqr
    eqtrd
    @0
    @5
    cr
    wcel
    @3
    @8
    adantr
    eqeltrd
    ex
    impbid2
end
