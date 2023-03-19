include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "crab.mm"
include "wceq.mm"
include "elex.mm"
include "clpl.mm"
include "cfv.mm"
include "ccvr.mm"
include "clln.mm"
include "cbs.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "breqd.mm"
include "rexeqbidv.mm"
include "rabeqbidv.mm"
include "df-lplanes.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem lplnset
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cK: class K
  let cN: class N
  let vk: setvar k
  assume lplnset.b: |- B = ( Base ` K )
  assume lplnset.c: |- C = ( <o ` K )
  assume lplnset.n: |- N = ( LLines ` K )
  assume lplnset.p: |- P = ( LPlanes ` K )

  disjoint N y
  disjoint B x
  disjoint x y
  disjoint K y
  disjoint K x
  disjoint k y
  disjoint N k
  disjoint k x
  disjoint B k
  disjoint C k
  disjoint K k
  assert |- ( K e. A -> P = { x e. B | E. y e. N y C x } )

  proof
    cK
    cA
    wcel
    cK
    cvv
    wcel
    #
    cP
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
    cN
    wrex
    #
    vx
    cB
    crab
    #
    wceq
    cK
    cA
    elex
    @0
    cP
    cK
    clpl
    cfv
    @5
    lplnset.p
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
    vy
    @6
    clln
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
    clpl
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
    lplnset.b
    syl6eqr
    @12
    @8
    @3
    vy
    @9
    cN
    @12
    @9
    cK
    clln
    cfv
    cN
    @6
    cK
    clln
    fveq2
    lplnset.n
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
    lplnset.c
    syl6eqr
    breqd
    rexeqbidv
    rabeqbidv
    vx
    vk
    vy
    df-lplanes
    @4
    vx
    cB
    cB
    @13
    cvv
    lplnset.b
    cK
    cbs
    fvex
    eqeltri
    rabex
    fvmpt
    syl5eq
    syl
end
