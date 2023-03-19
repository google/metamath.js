include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "w3a.mm"
include "ccj.mm"
include "cfv.mm"
include "csm.mm"
include "co.mm"
include "csp.mm"
include "cmul.mm"
include "wceq.mm"
include "cjcl.mm"
include "his5.mm"
include "syl3an1.mm"
include "cjcj.mm"
include "oveq1d.mm"
include "3ad2ant1.mm"
include "eqtrd.mm"

theorem his52
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. ~H /\ C e. ~H ) -> ( B .ih ( ( * ` A ) .h C ) ) = ( A x. ( B .ih C ) ) )

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
    cB
    cA
    ccj
    cfv
    #
    cC
    csm
    co
    csp
    co
    #
    @3
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
    cA
    @6
    cmul
    co
    #
    @0
    @3
    cc
    wcel
    @1
    @2
    @4
    @7
    wceq
    cA
    cjcl
    @3
    cB
    cC
    his5
    syl3an1
    @0
    @1
    @7
    @8
    wceq
    @2
    @0
    @5
    cA
    @6
    cmul
    cA
    cjcj
    oveq1d
    3ad2ant1
    eqtrd
end
