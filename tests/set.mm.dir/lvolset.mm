include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "crab.mm"
include "wceq.mm"
include "elex.mm"
include "clvol.mm"
include "cfv.mm"
include "ccvr.mm"
include "clpl.mm"
include "cbs.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "breqd.mm"
include "rexeqbidv.mm"
include "rabeqbidv.mm"
include "df-lvols.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem lvolset
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cK: class K
  let cV: class V
  let vk: setvar k
  assume lvolset.b: |- B = ( Base ` K )
  assume lvolset.c: |- C = ( <o ` K )
  assume lvolset.p: |- P = ( LPlanes ` K )
  assume lvolset.v: |- V = ( LVols ` K )

  disjoint P y
  disjoint B x
  disjoint x y
  disjoint K y
  disjoint K x
  disjoint k y
  disjoint P k
  disjoint k x
  disjoint B k
  disjoint C k
  disjoint K k
  assert |- ( K e. A -> V = { x e. B | E. y e. P y C x } )

  proof
    cK
    cA
    wcel
    cK
    cvv
    wcel
    #
    cV
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
    wceq
    cK
    cA
    elex
    @0
    cV
    cK
    clvol
    cfv
    @5
    lvolset.v
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
    clpl
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
    clvol
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
    lvolset.b
    syl6eqr
    @12
    @8
    @3
    vy
    @9
    cP
    @12
    @9
    cK
    clpl
    cfv
    cP
    @6
    cK
    clpl
    fveq2
    lvolset.p
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
    lvolset.c
    syl6eqr
    breqd
    rexeqbidv
    rabeqbidv
    vx
    vk
    vy
    df-lvols
    @4
    vx
    cB
    cB
    @13
    cvv
    lvolset.b
    cK
    cbs
    fvex
    eqeltri
    rabex
    fvmpt
    syl5eq
    syl
end
