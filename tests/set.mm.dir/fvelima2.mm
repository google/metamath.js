include "cima.mm"
include "wcel.mm"
include "wfn.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "cfv.mm"
include "wceq.mm"
include "cin.mm"
include "wrex.mm"
include "id.mm"
include "elimag.mm"
include "mpbid.mm"
include "df-rex.mm"
include "sylib.mm"
include "fnbr.mm"
include "adantrl.mm"
include "simprl.mm"
include "elind.mm"
include "wfun.mm"
include "fnfun.mm"
include "funbrfv.mm"
include "imp.mm"
include "sylan.mm"
include "jca.mm"
include "ex.mm"
include "eximdv.mm"
include "sylibr.mm"
include "sylan2.mm"

theorem fvelima2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint F x
  assert |- ( ( F Fn A /\ B e. ( F " C ) ) -> E. x e. ( A i^i C ) ( F ` x ) = B )

  proof
    cB
    cF
    cC
    cima
    #
    wcel
    #
    cF
    cA
    wfn
    #
    vx
    cv
    #
    cC
    wcel
    #
    @3
    cB
    cF
    wbr
    #
    wa
    #
    vx
    wex
    #
    @3
    cF
    cfv
    cB
    wceq
    #
    vx
    cA
    cC
    cin
    #
    wrex
    #
    @1
    @5
    vx
    cC
    wrex
    #
    @7
    @1
    @1
    @11
    @1
    id
    vx
    cB
    cF
    cC
    @0
    elimag
    mpbid
    @5
    vx
    cC
    df-rex
    sylib
    @2
    @7
    wa
    @3
    @9
    wcel
    #
    @8
    wa
    #
    vx
    wex
    #
    @10
    @2
    @7
    @14
    @2
    @6
    @13
    vx
    @2
    @6
    @13
    @2
    @6
    wa
    #
    @12
    @8
    @15
    cA
    cC
    @3
    @2
    @5
    @3
    cA
    wcel
    @4
    cA
    @3
    cB
    cF
    fnbr
    adantrl
    @2
    @4
    @5
    simprl
    elind
    @2
    @5
    @8
    @4
    @2
    cF
    wfun
    #
    @5
    @8
    cA
    cF
    fnfun
    @16
    @5
    @8
    @3
    cB
    cF
    funbrfv
    imp
    sylan
    adantrl
    jca
    ex
    eximdv
    imp
    @8
    vx
    @9
    df-rex
    sylibr
    sylan2
end
