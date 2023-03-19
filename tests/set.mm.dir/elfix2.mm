include "cfix.mm"
include "wcel.mm"
include "cvv.mm"
include "wbr.mm"
include "elex.mm"
include "brrelexi.mm"
include "cv.mm"
include "eleq1.mm"
include "wceq.mm"
include "wb.mm"
include "breq12.mm"
include "anidms.mm"
include "vex.mm"
include "elfix.mm"
include "vtoclbg.mm"
include "pm5.21nii.mm"

theorem elfix2
  let cA: class A
  let cR: class R
  let vx: setvar x
  assume elfix2.1: |- Rel R


  assert |- ( A e. Fix R <-> A R A )

  proof
    cA
    cR
    cfix
    #
    wcel
    #
    cA
    cvv
    wcel
    cA
    cA
    cR
    wbr
    #
    cA
    @0
    elex
    cA
    cA
    cR
    elfix2.1
    brrelexi
    vx
    cv
    #
    @0
    wcel
    @3
    @3
    cR
    wbr
    #
    @1
    @2
    vx
    cA
    cvv
    @3
    cA
    @0
    eleq1
    @3
    cA
    wceq
    @4
    @2
    wb
    @3
    cA
    @3
    cA
    cR
    breq12
    anidms
    @3
    cR
    vx
    vex
    elfix
    vtoclbg
    pm5.21nii
end
