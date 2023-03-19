include "cr.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cvol.mm"
include "cfv.mm"
include "citg.mm"
include "carea.mm"
include "cdm.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "simpl.mm"
include "imaeq1d.mm"
include "fveq2d.mm"
include "itgeq2dv.mm"
include "dfarea.mm"
include "itgex.mm"
include "fvmpt.mm"

theorem areaval
  let vx: setvar x
  let cS: class S
  let vs: setvar s
  let vt: setvar t
  let vy: setvar y
  let cA: class A

  disjoint S x
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint A s
  disjoint t x
  disjoint t y
  disjoint A t
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint S s
  assert |- ( S e. dom area -> ( area ` S ) = S. RR ( vol ` ( S " { x } ) ) _d x )

  proof
    vs
    cS
    vx
    cr
    vs
    cv
    #
    vx
    cv
    #
    csn
    #
    cima
    #
    cvol
    cfv
    #
    citg
    vx
    cr
    cS
    @2
    cima
    #
    cvol
    cfv
    #
    citg
    carea
    cdm
    carea
    @0
    cS
    wceq
    #
    vx
    cr
    @4
    @6
    @7
    @1
    cr
    wcel
    #
    wa
    #
    @3
    @5
    cvol
    @9
    @0
    cS
    @2
    @7
    @8
    simpl
    imaeq1d
    fveq2d
    itgeq2dv
    vx
    vs
    dfarea
    vx
    cr
    @6
    itgex
    fvmpt
end
