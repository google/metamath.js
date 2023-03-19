include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "wcel.mm"
include "cuni.mm"
include "cvv.mm"
include "wa.mm"
include "wral.mm"
include "uniexg.mm"
include "ciun.mm"
include "wi.mm"
include "simpl.mm"
include "ralimi.mm"
include "dfiun2g.mm"
include "eleq1d.mm"
include "biimprd.mm"
include "syl.mm"
include "wss.mm"
include "simpr.mm"
include "csn.mm"
include "iunid.mm"
include "snssi.mm"
include "ss2iun.mm"
include "syl5eqssr.mm"
include "ssexg.mm"
include "ex.mm"
include "3syl.mm"
include "syld.mm"
include "syl5.mm"

theorem abnexg
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cV: class V
  let cW: class W

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint F y
  assert |- ( A. x e. A ( F e. V /\ x e. F ) -> ( { y | E. x e. A y = F } e. W -> A e. _V ) )

  proof
    vy
    cv
    cF
    wceq
    vx
    cA
    wrex
    vy
    cab
    #
    cW
    wcel
    @0
    cuni
    #
    cvv
    wcel
    #
    cF
    cV
    wcel
    #
    vx
    cv
    #
    cF
    wcel
    #
    wa
    #
    vx
    cA
    wral
    #
    cA
    cvv
    wcel
    #
    @0
    cW
    uniexg
    @7
    @2
    vx
    cA
    cF
    ciun
    #
    cvv
    wcel
    #
    @8
    @7
    @3
    vx
    cA
    wral
    #
    @2
    @10
    wi
    @6
    @3
    vx
    cA
    @3
    @5
    simpl
    ralimi
    @11
    @10
    @2
    @11
    @9
    @1
    cvv
    vx
    vy
    cA
    cF
    cV
    dfiun2g
    eleq1d
    biimprd
    syl
    @7
    @5
    vx
    cA
    wral
    #
    cA
    @9
    wss
    #
    @10
    @8
    wi
    @6
    @5
    vx
    cA
    @3
    @5
    simpr
    ralimi
    @12
    cA
    vx
    cA
    @4
    csn
    #
    ciun
    #
    @9
    vx
    cA
    iunid
    @12
    @14
    cF
    wss
    #
    vx
    cA
    wral
    @15
    @9
    wss
    @5
    @16
    vx
    cA
    @4
    cF
    snssi
    ralimi
    vx
    cA
    @14
    cF
    ss2iun
    syl
    syl5eqssr
    @13
    @10
    @8
    cA
    @9
    cvv
    ssexg
    ex
    3syl
    syld
    syl5
end
