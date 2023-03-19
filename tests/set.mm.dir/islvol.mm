include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "crab.mm"
include "wa.mm"
include "lvolset.mm"
include "eleq2d.mm"
include "wceq.mm"
include "breq2.mm"
include "rexbidv.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem islvol
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cK: class K
  let cV: class V
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume lvolset.b: |- B = ( Base ` K )
  assume lvolset.c: |- C = ( <o ` K )
  assume lvolset.p: |- P = ( LPlanes ` K )
  assume lvolset.v: |- V = ( LVols ` K )

  disjoint P y
  disjoint K y
  disjoint X y
  disjoint k y
  disjoint P k
  disjoint k x
  disjoint B k
  disjoint B x
  disjoint C k
  disjoint K k
  disjoint x y
  disjoint K x
  disjoint P x
  disjoint C x
  disjoint X x
  assert |- ( K e. A -> ( X e. V <-> ( X e. B /\ E. y e. P y C X ) ) )

  proof
    cK
    cA
    wcel
    #
    cX
    cV
    wcel
    cX
    vy
    cv
    #
    vx
    cv
    #
    cC
    wbr
    #
    vy
    cP
    wrex
    #
    vx
    cB
    crab
    #
    wcel
    cX
    cB
    wcel
    @1
    cX
    cC
    wbr
    #
    vy
    cP
    wrex
    #
    wa
    @0
    cV
    @5
    cX
    vx
    vy
    cA
    cB
    cC
    cP
    cK
    cV
    lvolset.b
    lvolset.c
    lvolset.p
    lvolset.v
    lvolset
    eleq2d
    @4
    @7
    vx
    cX
    cB
    @2
    cX
    wceq
    @3
    @6
    vy
    cP
    @2
    cX
    @1
    cC
    breq2
    rexbidv
    elrab
    syl6bb
end
