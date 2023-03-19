include "carea.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cvol.mm"
include "ccnv.mm"
include "cr.mm"
include "wcel.mm"
include "wral.mm"
include "cfv.mm"
include "cmpt.mm"
include "cibl.mm"
include "wa.mm"
include "cxp.mm"
include "cpw.mm"
include "crab.mm"
include "citg.mm"
include "cdm.mm"
include "df-area.mm"
include "wceq.mm"
include "itgex.mm"
include "dmmpti.mm"
include "mpteq1.mm"
include "ax-mp.mm"
include "eqtr4i.mm"

theorem dfarea
  let vx: setvar x
  let vs: setvar s
  let vt: setvar t
  let vy: setvar y
  let cA: class A
  let cS: class S

  disjoint s x
  disjoint s t
  disjoint s y
  disjoint A s
  disjoint t x
  disjoint t y
  disjoint A t
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint S s
  disjoint S x
  assert |- area = ( s e. dom area |-> S. RR ( vol ` ( s " { x } ) ) _d x )

  proof
    carea
    vs
    vy
    cv
    vx
    cv
    csn
    #
    cima
    #
    cvol
    ccnv
    cr
    cima
    wcel
    vx
    cr
    wral
    vx
    cr
    @1
    cvol
    cfv
    cmpt
    cibl
    wcel
    wa
    vy
    cr
    cr
    cxp
    cpw
    crab
    #
    vx
    cr
    vs
    cv
    @0
    cima
    cvol
    cfv
    #
    citg
    #
    cmpt
    #
    vs
    carea
    cdm
    #
    @4
    cmpt
    #
    vx
    vy
    vs
    df-area
    #
    @6
    @2
    wceq
    @7
    @5
    wceq
    vs
    @2
    @4
    carea
    vx
    cr
    @3
    itgex
    @8
    dmmpti
    vs
    @6
    @2
    @4
    mpteq1
    ax-mp
    eqtr4i
end
