include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "w3a.mm"
include "csm.mm"
include "co.mm"
include "csp.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "wceq.mm"
include "wa.mm"
include "hvmulcl.mm"
include "ax-his1.mm"
include "sylan2.mm"
include "3impb.mm"
include "3com12.mm"
include "ax-his3.mm"
include "3com23.mm"
include "fveq2d.mm"
include "hicl.mm"
include "cjmul.mm"
include "3adant1.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "3eqtrd.mm"

theorem his5
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. ~H /\ C e. ~H ) -> ( B .ih ( A .h C ) ) = ( ( * ` A ) x. ( B .ih C ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    chil
    wcel
    #
    cC
    chil
    wcel
    #
    w3a
    #
    cB
    cA
    cC
    csm
    co
    #
    csp
    co
    #
    @4
    cB
    csp
    co
    #
    ccj
    cfv
    #
    cA
    cC
    cB
    csp
    co
    #
    cmul
    co
    #
    ccj
    cfv
    #
    cA
    ccj
    cfv
    #
    cB
    cC
    csp
    co
    #
    cmul
    co
    #
    @1
    @0
    @2
    @5
    @7
    wceq
    #
    @1
    @0
    @2
    @14
    @0
    @2
    wa
    @1
    @4
    chil
    wcel
    @14
    cA
    cC
    hvmulcl
    cB
    @4
    ax-his1
    sylan2
    3impb
    3com12
    @3
    @6
    @9
    ccj
    @0
    @2
    @1
    @6
    @9
    wceq
    cA
    cC
    cB
    ax-his3
    3com23
    fveq2d
    @3
    @10
    @11
    @8
    ccj
    cfv
    #
    cmul
    co
    #
    @13
    @0
    @2
    @1
    @10
    @16
    wceq
    #
    @0
    @2
    @1
    @17
    @2
    @1
    wa
    @0
    @8
    cc
    wcel
    @17
    cC
    cB
    hicl
    cA
    @8
    cjmul
    sylan2
    3impb
    3com23
    @3
    @12
    @15
    @11
    cmul
    @1
    @2
    @12
    @15
    wceq
    @0
    cB
    cC
    ax-his1
    3adant1
    oveq2d
    eqtr4d
    3eqtrd
end
