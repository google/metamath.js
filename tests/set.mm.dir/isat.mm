include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "wa.mm"
include "pats.mm"
include "eleq2d.mm"
include "breq2.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem isat
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cK: class K
  let c.0: class .0.
  let vx: setvar x
  assume isatom.b: |- B = ( Base ` K )
  assume isatom.z: |- .0. = ( 0. ` K )
  assume isatom.c: |- C = ( <o ` K )
  assume isatom.a: |- A = ( Atoms ` K )


  assert |- ( K e. D -> ( P e. A <-> ( P e. B /\ .0. C P ) ) )

  proof
    cK
    cD
    wcel
    #
    cP
    cA
    wcel
    cP
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
    wcel
    cP
    cB
    wcel
    c.0
    cP
    cC
    wbr
    #
    wa
    @0
    cA
    @3
    cP
    vx
    cA
    cB
    cC
    cD
    cK
    c.0
    isatom.b
    isatom.z
    isatom.c
    isatom.a
    pats
    eleq2d
    @2
    @4
    vx
    cP
    cB
    @1
    cP
    c.0
    cC
    breq2
    elrab
    syl6bb
end
