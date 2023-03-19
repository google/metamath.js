include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "crab.mm"
include "wa.mm"
include "llnset.mm"
include "eleq2d.mm"
include "wceq.mm"
include "breq2.mm"
include "rexbidv.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem islln
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
  assert |- ( K e. D -> ( X e. N <-> ( X e. B /\ E. p e. A p C X ) ) )

  proof
    cK
    cD
    wcel
    #
    cX
    cN
    wcel
    cX
    vp
    cv
    #
    vx
    cv
    #
    cC
    wbr
    #
    vp
    cA
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
    vp
    cA
    wrex
    #
    wa
    @0
    cN
    @5
    cX
    vx
    cA
    cB
    cC
    cD
    cK
    cN
    vp
    llnset.b
    llnset.c
    llnset.a
    llnset.n
    llnset
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
    vp
    cA
    @2
    cX
    @1
    cC
    breq2
    rexbidv
    elrab
    syl6bb
end
