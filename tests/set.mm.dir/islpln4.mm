include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "islpln.mm"
include "baibd.mm"

theorem islpln4
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cK: class K
  let cN: class N
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume lplnset.b: |- B = ( Base ` K )
  assume lplnset.c: |- C = ( <o ` K )
  assume lplnset.n: |- N = ( LLines ` K )
  assume lplnset.p: |- P = ( LPlanes ` K )

  disjoint N y
  disjoint K y
  disjoint X y
  disjoint k y
  disjoint N k
  disjoint k x
  disjoint B k
  disjoint B x
  disjoint C k
  disjoint K k
  disjoint x y
  disjoint K x
  disjoint N x
  disjoint C x
  disjoint X x
  assert |- ( ( K e. A /\ X e. B ) -> ( X e. P <-> E. y e. N y C X ) )

  proof
    cK
    cA
    wcel
    cX
    cP
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
    cN
    wrex
    vy
    cA
    cB
    cC
    cP
    cK
    cN
    cX
    lplnset.b
    lplnset.c
    lplnset.n
    lplnset.p
    islpln
    baibd
end
