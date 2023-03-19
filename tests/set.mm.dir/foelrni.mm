include "wfo.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "crn.mm"
include "forn.mm"
include "eleq2d.mm"
include "wfn.mm"
include "wb.mm"
include "fofn.mm"
include "fvelrnb.mm"
include "syl.mm"
include "bitr3d.mm"
include "biimpa.mm"

theorem foelrni
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cY: class Y
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint Y x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint F y
  assert |- ( ( F : A -onto-> B /\ Y e. B ) -> E. x e. A ( F ` x ) = Y )

  proof
    cA
    cB
    cF
    wfo
    #
    cY
    cB
    wcel
    #
    vx
    cv
    cF
    cfv
    cY
    wceq
    vx
    cA
    wrex
    #
    @0
    cY
    cF
    crn
    #
    wcel
    #
    @1
    @2
    @0
    @3
    cB
    cY
    cA
    cB
    cF
    forn
    eleq2d
    @0
    cF
    cA
    wfn
    @4
    @2
    wb
    cA
    cB
    cF
    fofn
    vx
    cA
    cY
    cF
    fvelrnb
    syl
    bitr3d
    biimpa
end
