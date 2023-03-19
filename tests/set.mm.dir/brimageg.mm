include "cv.mm"
include "cimage.mm"
include "wbr.mm"
include "cima.mm"
include "wceq.mm"
include "wb.mm"
include "breq1.mm"
include "imaeq2.mm"
include "eqeq2d.mm"
include "bibi12d.mm"
include "breq2.mm"
include "eqeq1.mm"
include "vex.mm"
include "brimage.mm"
include "vtocl2g.mm"

theorem brimageg
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. V /\ B e. W ) -> ( A Image R B <-> B = ( R " A ) ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cR
    cimage
    #
    wbr
    #
    @1
    cR
    @0
    cima
    #
    wceq
    #
    wb
    cA
    @1
    @2
    wbr
    #
    @1
    cR
    cA
    cima
    #
    wceq
    #
    wb
    cA
    cB
    @2
    wbr
    #
    cB
    @7
    wceq
    #
    wb
    vx
    vy
    cA
    cB
    cV
    cW
    @0
    cA
    wceq
    #
    @3
    @6
    @5
    @8
    @0
    cA
    @1
    @2
    breq1
    @11
    @4
    @7
    @1
    @0
    cA
    cR
    imaeq2
    eqeq2d
    bibi12d
    @1
    cB
    wceq
    @6
    @9
    @8
    @10
    @1
    cB
    cA
    @2
    breq2
    @1
    cB
    @7
    eqeq1
    bibi12d
    @0
    @1
    cR
    vx
    vex
    vy
    vex
    brimage
    vtocl2g
end
