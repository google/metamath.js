include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "crab.mm"
include "wceq.mm"
include "elex.mm"
include "clln.mm"
include "cfv.mm"
include "ccvr.mm"
include "catm.mm"
include "cbs.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "breqd.mm"
include "rexeqbidv.mm"
include "rabeqbidv.mm"
include "df-llines.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem llnset
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cK: class K
  let cN: class N
  let vp: setvar p
  let vk: setvar k
  assume llnset.b: |- B = ( Base ` K )
  assume llnset.c: |- C = ( <o ` K )
  assume llnset.a: |- A = ( Atoms ` K )
  assume llnset.n: |- N = ( LLines ` K )

  disjoint A p
  disjoint B x
  disjoint p x
  disjoint K p
  disjoint K x
  disjoint k p
  disjoint A k
  disjoint k x
  disjoint B k
  disjoint C k
  disjoint K k
  assert |- ( K e. D -> N = { x e. B | E. p e. A p C x } )

  proof
    cK
    cD
    wcel
    cK
    cvv
    wcel
    #
    cN
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
    wceq
    cK
    cD
    elex
    @0
    cN
    cK
    clln
    cfv
    @5
    llnset.n
    vk
    cK
    @1
    @2
    vk
    cv
    #
    ccvr
    cfv
    #
    wbr
    #
    vp
    @6
    catm
    cfv
    #
    wrex
    #
    vx
    @6
    cbs
    cfv
    #
    crab
    @5
    cvv
    clln
    @6
    cK
    wceq
    #
    @10
    @4
    vx
    @11
    cB
    @12
    @11
    cK
    cbs
    cfv
    #
    cB
    @6
    cK
    cbs
    fveq2
    llnset.b
    syl6eqr
    @12
    @8
    @3
    vp
    @9
    cA
    @12
    @9
    cK
    catm
    cfv
    cA
    @6
    cK
    catm
    fveq2
    llnset.a
    syl6eqr
    @12
    @7
    cC
    @1
    @2
    @12
    @7
    cK
    ccvr
    cfv
    cC
    @6
    cK
    ccvr
    fveq2
    llnset.c
    syl6eqr
    breqd
    rexeqbidv
    rabeqbidv
    vx
    vk
    vp
    df-llines
    @4
    vx
    cB
    cB
    @13
    cvv
    llnset.b
    cK
    cbs
    fvex
    eqeltri
    rabex
    fvmpt
    syl5eq
    syl
end
