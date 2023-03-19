include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "chil.mm"
include "csm.mm"
include "co.mm"
include "csp.mm"
include "cmul.mm"
include "ccj.mm"
include "cfv.mm"
include "wceq.mm"
include "his5.mm"
include "3expb.mm"
include "adantll.mm"
include "oveq2d.mm"
include "simpll.mm"
include "simprl.mm"
include "hvmulcl.mm"
include "ad2ant2l.mm"
include "ax-his3.mm"
include "syl3anc.mm"
include "cjcl.mm"
include "ad2antlr.mm"
include "hicl.mm"
include "adantl.mm"
include "mulassd.mm"
include "3eqtr4d.mm"

theorem his35
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. CC /\ B e. CC ) /\ ( C e. ~H /\ D e. ~H ) ) -> ( ( A .h C ) .ih ( B .h D ) ) = ( ( A x. ( * ` B ) ) x. ( C .ih D ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cC
    chil
    wcel
    #
    cD
    chil
    wcel
    #
    wa
    #
    wa
    #
    cA
    cC
    cB
    cD
    csm
    co
    #
    csp
    co
    #
    cmul
    co
    #
    cA
    cB
    ccj
    cfv
    #
    cC
    cD
    csp
    co
    #
    cmul
    co
    #
    cmul
    co
    cA
    cC
    csm
    co
    @7
    csp
    co
    #
    cA
    @10
    cmul
    co
    @11
    cmul
    co
    @6
    @8
    @12
    cA
    cmul
    @1
    @5
    @8
    @12
    wceq
    #
    @0
    @1
    @3
    @4
    @14
    cB
    cC
    cD
    his5
    3expb
    adantll
    oveq2d
    @6
    @0
    @3
    @7
    chil
    wcel
    #
    @13
    @9
    wceq
    @0
    @1
    @5
    simpll
    #
    @2
    @3
    @4
    simprl
    @1
    @4
    @15
    @0
    @3
    cB
    cD
    hvmulcl
    ad2ant2l
    cA
    cC
    @7
    ax-his3
    syl3anc
    @6
    cA
    @10
    @11
    @16
    @1
    @10
    cc
    wcel
    @0
    @5
    cB
    cjcl
    ad2antlr
    @5
    @11
    cc
    wcel
    @2
    cC
    cD
    hicl
    adantl
    mulassd
    3eqtr4d
end
