include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "clcm.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "wne.mm"
include "lcmn0cl.mm"
include "nnne0d.mm"
include "ex.mm"
include "necon4bd.mm"
include "oveq1.mm"
include "0z.mm"
include "lcmcom.mm"
include "mpan2.mm"
include "lcm0val.mm"
include "eqtr3d.mm"
include "sylan9eqr.mm"
include "adantll.mm"
include "oveq2.mm"
include "adantlr.mm"
include "jaodan.mm"
include "impbid.mm"

theorem lcmeq0
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( ( M lcm N ) = 0 <-> ( M = 0 \/ N = 0 ) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cM
    cN
    clcm
    co
    #
    cc0
    wceq
    #
    cM
    cc0
    wceq
    #
    cN
    cc0
    wceq
    #
    wo
    #
    @2
    @7
    @3
    cc0
    @2
    @7
    wn
    #
    @3
    cc0
    wne
    @2
    @8
    wa
    @3
    cM
    cN
    lcmn0cl
    nnne0d
    ex
    necon4bd
    @2
    @7
    @4
    @2
    @5
    @4
    @6
    @1
    @5
    @4
    @0
    @5
    @1
    @3
    cc0
    cN
    clcm
    co
    #
    cc0
    cM
    cc0
    cN
    clcm
    oveq1
    @1
    cN
    cc0
    clcm
    co
    #
    @9
    cc0
    @1
    cc0
    cz
    wcel
    @10
    @9
    wceq
    0z
    cN
    cc0
    lcmcom
    mpan2
    cN
    lcm0val
    eqtr3d
    sylan9eqr
    adantll
    @0
    @6
    @4
    @1
    @6
    @0
    @3
    cM
    cc0
    clcm
    co
    cc0
    cN
    cc0
    cM
    clcm
    oveq2
    cM
    lcm0val
    sylan9eqr
    adantlr
    jaodan
    ex
    impbid
end
