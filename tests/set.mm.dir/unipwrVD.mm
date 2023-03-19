include "cpw.mm"
include "cuni.mm"
include "cv.mm"
include "wcel.mm"
include "csn.mm"
include "vex.mm"
include "snid.mm"
include "idn1.mm"
include "snelpwi.mm"
include "e1a.mm"
include "elunii.mm"
include "e01an.mm"
include "in1.mm"
include "ssriv.mm"

theorem unipwrVD
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
    #
    @2
    @1
    wcel
    #
    @2
    @2
    csn
    #
    wcel
    @3
    @5
    @0
    wcel
    #
    @4
    @2
    vx
    vex
    snid
    @3
    @3
    @6
    @3
    idn1
    @2
    cA
    snelpwi
    e1a
    @2
    @5
    @0
    elunii
    e01an
    in1
    ssriv
end
