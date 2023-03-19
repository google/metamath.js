include "wer.mm"
include "cv.mm"
include "wceq.mm"
include "cin.mm"
include "c0.mm"
include "wo.mm"
include "cqs.mm"
include "wral.mm"
include "wdisj.mm"
include "wcel.mm"
include "wa.mm"
include "simpl.mm"
include "simprl.mm"
include "simprr.mm"
include "qsdisj.mm"
include "ralrimivva.mm"
include "id.mm"
include "disjor.mm"
include "sylibr.mm"

theorem qsdisj2
  let vx: setvar x
  let cA: class A
  let cR: class R
  let cX: class X
  let vy: setvar y

  disjoint A x
  disjoint X x
  disjoint R x
  disjoint x y
  disjoint A y
  disjoint X y
  disjoint R y
  assert |- ( R Er X -> Disj_ x e. ( A /. R ) x )

  proof
    cX
    cR
    wer
    #
    vx
    cv
    #
    vy
    cv
    #
    wceq
    #
    @1
    @2
    cin
    c0
    wceq
    wo
    #
    vy
    cA
    cR
    cqs
    #
    wral
    vx
    @5
    wral
    vx
    @5
    @1
    wdisj
    @0
    @4
    vx
    vy
    @5
    @5
    @0
    @1
    @5
    wcel
    #
    @2
    @5
    wcel
    #
    wa
    #
    wa
    cA
    @1
    @2
    cR
    cX
    @0
    @8
    simpl
    @0
    @6
    @7
    simprl
    @0
    @6
    @7
    simprr
    qsdisj
    ralrimivva
    @5
    @1
    @2
    vx
    vy
    @3
    id
    disjor
    sylibr
end
