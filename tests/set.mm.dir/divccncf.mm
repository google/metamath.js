include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cv.mm"
include "cmul.mm"
include "cmpt.mm"
include "ccncf.mm"
include "wceq.mm"
include "divrec2.mm"
include "3expb.mm"
include "ancoms.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"
include "reccl.mm"
include "eqid.mm"
include "mulc1cncf.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem divccncf
  let vx: setvar x
  let cA: class A
  let cF: class F
  assume divccncf.1: |- F = ( x e. CC |-> ( x / A ) )

  disjoint A x
  assert |- ( ( A e. CC /\ A =/= 0 ) -> F e. ( CC -cn-> CC ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    cF
    vx
    cc
    c1
    cA
    cdiv
    co
    #
    vx
    cv
    #
    cmul
    co
    #
    cmpt
    #
    cc
    cc
    ccncf
    co
    #
    @2
    cF
    vx
    cc
    @4
    cA
    cdiv
    co
    #
    cmpt
    @6
    divccncf.1
    @2
    vx
    cc
    @8
    @5
    @4
    cc
    wcel
    #
    @2
    @8
    @5
    wceq
    #
    @9
    @0
    @1
    @10
    @4
    cA
    divrec2
    3expb
    ancoms
    mpteq2dva
    syl5eq
    @2
    @3
    cc
    wcel
    @6
    @7
    wcel
    cA
    reccl
    vx
    @3
    @6
    @6
    eqid
    mulc1cncf
    syl
    eqeltrd
end
