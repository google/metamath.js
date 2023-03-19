include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wfn.mm"
include "wsbc.mm"
include "wb.mm"
include "fneq2.mm"
include "sbcie2g.mm"
include "ax-mp.mm"

theorem bnj90
  let vx: setvar x
  let vz: setvar z
  let cY: class Y
  let vy: setvar y
  assume bnj90.1: |- Y e. _V

  disjoint x z
  disjoint Y y
  disjoint x y
  disjoint y z
  assert |- ( [. Y / x ]. z Fn x <-> z Fn Y )

  proof
    cY
    cvv
    wcel
    vz
    cv
    #
    vx
    cv
    #
    wfn
    #
    vx
    cY
    wsbc
    @0
    cY
    wfn
    #
    wb
    bnj90.1
    @2
    @0
    vy
    cv
    #
    wfn
    @3
    vx
    vy
    cY
    cvv
    @1
    @4
    @0
    fneq2
    @4
    cY
    @0
    fneq2
    sbcie2g
    ax-mp
end
