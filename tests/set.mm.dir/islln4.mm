include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "islln.mm"
include "baibd.mm"

theorem islln4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cK: class K
  let cN: class N
  let cX: class X
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x
  assume llnset.b: |- B = ( Base ` K )
  assume llnset.c: |- C = ( <o ` K )
  assume llnset.a: |- A = ( Atoms ` K )
  assume llnset.n: |- N = ( LLines ` K )

  disjoint A p
  disjoint K p
  disjoint X p
  disjoint k p
  disjoint A k
  disjoint k x
  disjoint B k
  disjoint B x
  disjoint C k
  disjoint K k
  disjoint p x
  disjoint K x
  disjoint A x
  disjoint C x
  disjoint X x
  assert |- ( ( K e. D /\ X e. B ) -> ( X e. N <-> E. p e. A p C X ) )

  proof
    cK
    cD
    wcel
    cX
    cN
    wcel
    cX
    cB
    wcel
    vp
    cv
    cX
    cC
    wbr
    vp
    cA
    wrex
    cA
    cB
    cC
    cD
    cK
    cN
    cX
    vp
    llnset.b
    llnset.c
    llnset.a
    llnset.n
    islln
    baibd
end
