include "char.mm"
include "cfv.mm"
include "wcel.mm"
include "cvv.mm"
include "con0.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "elfvex.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "adantl.mm"
include "cv.mm"
include "crab.mm"
include "harval.mm"
include "eleq2d.mm"
include "breq1.mm"
include "elrab.mm"
include "syl6bb.mm"
include "pm5.21nii.mm"

theorem elharval
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y


  assert |- ( Y e. ( har ` X ) <-> ( Y e. On /\ Y ~<_ X ) )

  proof
    cY
    cX
    char
    cfv
    #
    wcel
    #
    cX
    cvv
    wcel
    #
    cY
    con0
    wcel
    #
    cY
    cX
    cdom
    wbr
    #
    wa
    #
    cY
    cX
    char
    elfvex
    @4
    @2
    @3
    cY
    cX
    cdom
    reldom
    brrelex2i
    adantl
    @2
    @1
    cY
    vy
    cv
    #
    cX
    cdom
    wbr
    #
    vy
    con0
    crab
    #
    wcel
    @5
    @2
    @0
    @8
    cY
    vy
    cvv
    cX
    harval
    eleq2d
    @7
    @4
    vy
    cY
    con0
    @6
    cY
    cX
    cdom
    breq1
    elrab
    syl6bb
    pm5.21nii
end
