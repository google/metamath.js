include "cpw.mm"
include "cuni.mm"
include "cv.mm"
include "wcel.mm"
include "csn.mm"
include "vex.mm"
include "snid.mm"
include "snelpwi.mm"
include "elunii.mm"
include "sylancr.mm"
include "ssriv.mm"

theorem unipwr
  let cA: class A
  let vx: setvar x


  assert |- A C_ U. ~P A

  proof
    vx
    cA
    cA
    cpw
    #
    cuni
    #
    vx
    cv
    #
    cA
    wcel
    @2
    @2
    csn
    #
    wcel
    @3
    @0
    wcel
    @2
    @1
    wcel
    @2
    vx
    vex
    snid
    @2
    cA
    snelpwi
    @2
    @3
    @0
    elunii
    sylancr
    ssriv
end
