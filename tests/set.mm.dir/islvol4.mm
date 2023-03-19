include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "islvol.mm"
include "baibd.mm"

theorem islvol4
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
  assert |- ( ( K e. A /\ X e. B ) -> ( X e. V <-> E. y e. P y C X ) )

  proof
    cK
    cA
    wcel
    cX
    cV
    wcel
    cX
    cB
    wcel
    vy
    cv
    cX
    cC
    wbr
    vy
    cP
    wrex
    vy
    cA
    cB
    cC
    cP
    cK
    cV
    cX
    lvolset.b
    lvolset.c
    lvolset.p
    lvolset.v
    islvol
    baibd
end
