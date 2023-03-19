include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "wceq.mm"
include "elex.mm"
include "clh.mm"
include "cfv.mm"
include "cp1.mm"
include "ccvr.mm"
include "cbs.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eqidd.mm"
include "breq123d.mm"
include "rabeqbidv.mm"
include "df-lhyp.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem lhpset
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let c.1: class .1.
  let cH: class H
  let cK: class K
  let vk: setvar k
  let cW: class W
  assume lhpset.b: |- B = ( Base ` K )
  assume lhpset.u: |- .1. = ( 1. ` K )
  assume lhpset.c: |- C = ( <o ` K )
  assume lhpset.h: |- H = ( LHyp ` K )

  disjoint B w
  disjoint C w
  disjoint K w
  disjoint .1. w
  disjoint k w
  disjoint B k
  disjoint C k
  disjoint K k
  disjoint .1. k
  disjoint W w
  assert |- ( K e. A -> H = { w e. B | w C .1. } )

  proof
    cK
    cA
    wcel
    cK
    cvv
    wcel
    #
    cH
    vw
    cv
    #
    c.1
    cC
    wbr
    #
    vw
    cB
    crab
    #
    wceq
    cK
    cA
    elex
    @0
    cH
    cK
    clh
    cfv
    @3
    lhpset.h
    vk
    cK
    @1
    vk
    cv
    #
    cp1
    cfv
    #
    @4
    ccvr
    cfv
    #
    wbr
    #
    vw
    @4
    cbs
    cfv
    #
    crab
    @3
    cvv
    clh
    @4
    cK
    wceq
    #
    @7
    @2
    vw
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
    lhpset.b
    syl6eqr
    @9
    @1
    @1
    @5
    c.1
    @6
    cC
    @9
    @1
    eqidd
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
    lhpset.c
    syl6eqr
    @9
    @5
    cK
    cp1
    cfv
    c.1
    @4
    cK
    cp1
    fveq2
    lhpset.u
    syl6eqr
    breq123d
    rabeqbidv
    vw
    vk
    df-lhyp
    @2
    vw
    cB
    cB
    @10
    cvv
    lhpset.b
    cK
    cbs
    fvex
    eqeltri
    rabex
    fvmpt
    syl5eq
    syl
end
