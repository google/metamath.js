include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "cmin.mm"
include "simpl.mm"
include "simpr.mm"
include "subaddd.mm"
include "wi.mm"
include "eqcom.mm"
include "subid.mm"
include "adantr.mm"
include "eqtrd.mm"
include "ex.mm"
include "syl5bi.mm"
include "sylbird.mm"
include "oveq2.mm"
include "addid1.mm"
include "sylan9eqr.mm"
include "impbid.mm"

theorem addid0
  let cX: class X
  let cY: class Y


  assert |- ( ( X e. CC /\ Y e. CC ) -> ( ( X + Y ) = X <-> Y = 0 ) )

  proof
    cX
    cc
    wcel
    #
    cY
    cc
    wcel
    #
    wa
    #
    cX
    cY
    caddc
    co
    #
    cX
    wceq
    #
    cY
    cc0
    wceq
    #
    @2
    @4
    cX
    cX
    cmin
    co
    #
    cY
    wceq
    #
    @5
    @2
    cX
    cX
    cY
    @0
    @1
    simpl
    #
    @8
    @0
    @1
    simpr
    subaddd
    @0
    @7
    @5
    wi
    @1
    @7
    cY
    @6
    wceq
    #
    @0
    @5
    @6
    cY
    eqcom
    @0
    @9
    @5
    @0
    @9
    wa
    cY
    @6
    cc0
    @0
    @9
    simpr
    @0
    @6
    cc0
    wceq
    @9
    cX
    subid
    adantr
    eqtrd
    ex
    syl5bi
    adantr
    sylbird
    @0
    @5
    @4
    wi
    @1
    @0
    @5
    @4
    @5
    @0
    @3
    cX
    cc0
    caddc
    co
    cX
    cY
    cc0
    cX
    caddc
    oveq2
    cX
    addid1
    sylan9eqr
    ex
    adantr
    impbid
end
