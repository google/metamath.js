include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "wceq.mm"
include "elex.mm"
include "catm.mm"
include "cfv.mm"
include "cp0.mm"
include "ccvr.mm"
include "cbs.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "breqd.mm"
include "breq1d.mm"
include "bitrd.mm"
include "rabeqbidv.mm"
include "df-ats.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem pats
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cK: class K
  let c.0: class .0.
  let vp: setvar p
  assume patoms.b: |- B = ( Base ` K )
  assume patoms.z: |- .0. = ( 0. ` K )
  assume patoms.c: |- C = ( <o ` K )
  assume patoms.a: |- A = ( Atoms ` K )

  disjoint B x
  disjoint K x
  disjoint p x
  disjoint B p
  disjoint C p
  disjoint K p
  disjoint .0. p
  assert |- ( K e. D -> A = { x e. B | .0. C x } )

  proof
    cK
    cD
    wcel
    cK
    cvv
    wcel
    #
    cA
    c.0
    vx
    cv
    #
    cC
    wbr
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
    cA
    cK
    catm
    cfv
    @3
    patoms.a
    vp
    cK
    vp
    cv
    #
    cp0
    cfv
    #
    @1
    @4
    ccvr
    cfv
    #
    wbr
    #
    vx
    @4
    cbs
    cfv
    #
    crab
    @3
    cvv
    catm
    @4
    cK
    wceq
    #
    @7
    @2
    vx
    @8
    cB
    @9
    @8
    cK
    cbs
    cfv
    #
    cB
    @4
    cK
    cbs
    fveq2
    patoms.b
    syl6eqr
    @9
    @7
    @5
    @1
    cC
    wbr
    @2
    @9
    @6
    cC
    @5
    @1
    @9
    @6
    cK
    ccvr
    cfv
    cC
    @4
    cK
    ccvr
    fveq2
    patoms.c
    syl6eqr
    breqd
    @9
    @5
    c.0
    @1
    cC
    @9
    @5
    cK
    cp0
    cfv
    c.0
    @4
    cK
    cp0
    fveq2
    patoms.z
    syl6eqr
    breq1d
    bitrd
    rabeqbidv
    vp
    vx
    df-ats
    @2
    vx
    cB
    cB
    @10
    cvv
    patoms.b
    cK
    cbs
    fvex
    eqeltri
    rabex
    fvmpt
    syl5eq
    syl
end
