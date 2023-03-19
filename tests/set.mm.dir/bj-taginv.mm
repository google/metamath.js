include "cv.mm"
include "csn.mm"
include "bj-csngl.mm"
include "wcel.mm"
include "cab.mm"
include "bj-ctag.mm"
include "bj-snglinv.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "bj-sngltag.mm"
include "ax-mp.mm"
include "abbii.mm"
include "eqtri.mm"

theorem bj-taginv
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- A = { x | { x } e. tag A }

  proof
    cA
    vx
    cv
    #
    csn
    #
    cA
    bj-csngl
    wcel
    #
    vx
    cab
    @1
    cA
    bj-ctag
    wcel
    #
    vx
    cab
    vx
    cA
    bj-snglinv
    @2
    @3
    vx
    @0
    cvv
    wcel
    @2
    @3
    wb
    vx
    vex
    @0
    cA
    cvv
    bj-sngltag
    ax-mp
    abbii
    eqtri
end
