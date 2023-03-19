include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "wa.mm"
include "lhpset.mm"
include "eleq2d.mm"
include "breq1.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem islhp
  let cA: class A
  let cB: class B
  let cC: class C
  let c.1: class .1.
  let cH: class H
  let cK: class K
  let cW: class W
  let vk: setvar k
  let vw: setvar w
  assume lhpset.b: |- B = ( Base ` K )
  assume lhpset.u: |- .1. = ( 1. ` K )
  assume lhpset.c: |- C = ( <o ` K )
  assume lhpset.h: |- H = ( LHyp ` K )


  assert |- ( K e. A -> ( W e. H <-> ( W e. B /\ W C .1. ) ) )

  proof
    cK
    cA
    wcel
    #
    cW
    cH
    wcel
    cW
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
    wcel
    cW
    cB
    wcel
    cW
    c.1
    cC
    wbr
    #
    wa
    @0
    cH
    @3
    cW
    vw
    cA
    cB
    cC
    c.1
    cH
    cK
    lhpset.b
    lhpset.u
    lhpset.c
    lhpset.h
    lhpset
    eleq2d
    @2
    @4
    vw
    cW
    cB
    @1
    cW
    c.1
    cC
    breq1
    elrab
    syl6bb
end
