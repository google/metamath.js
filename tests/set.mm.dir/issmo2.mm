include "wf.mm"
include "con0.mm"
include "wss.mm"
include "word.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "w3a.mm"
include "cdm.mm"
include "wsmo.mm"
include "fss.mm"
include "ex.mm"
include "fdm.mm"
include "feq2d.mm"
include "sylibrd.mm"
include "wceq.mm"
include "wb.mm"
include "ordeq.mm"
include "syl.mm"
include "biimprd.mm"
include "raleqdv.mm"
include "3anim123d.mm"
include "dfsmo2.mm"
include "syl6ibr.mm"

theorem issmo2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F

  disjoint A x
  disjoint F x
  disjoint F y
  disjoint x y
  assert |- ( F : A --> B -> ( ( B C_ On /\ Ord A /\ A. x e. A A. y e. x ( F ` y ) e. ( F ` x ) ) -> Smo F ) )

  proof
    cA
    cB
    cF
    wf
    #
    cB
    con0
    wss
    #
    cA
    word
    #
    vy
    cv
    cF
    cfv
    vx
    cv
    #
    cF
    cfv
    wcel
    vy
    @3
    wral
    #
    vx
    cA
    wral
    #
    w3a
    cF
    cdm
    #
    con0
    cF
    wf
    #
    @6
    word
    #
    @4
    vx
    @6
    wral
    #
    w3a
    cF
    wsmo
    @0
    @1
    @7
    @2
    @8
    @5
    @9
    @0
    @1
    cA
    con0
    cF
    wf
    #
    @7
    @0
    @1
    @10
    cA
    cB
    con0
    cF
    fss
    ex
    @0
    @6
    cA
    con0
    cF
    cA
    cB
    cF
    fdm
    #
    feq2d
    sylibrd
    @0
    @8
    @2
    @0
    @6
    cA
    wceq
    @8
    @2
    wb
    @11
    @6
    cA
    ordeq
    syl
    biimprd
    @0
    @9
    @5
    @0
    @4
    vx
    @6
    cA
    @11
    raleqdv
    biimprd
    3anim123d
    vx
    vy
    cF
    dfsmo2
    syl6ibr
end
