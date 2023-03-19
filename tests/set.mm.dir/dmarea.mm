include "carea.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cvol.mm"
include "ccnv.mm"
include "cr.mm"
include "wral.mm"
include "cfv.mm"
include "cmpt.mm"
include "cibl.mm"
include "wa.mm"
include "cxp.mm"
include "cpw.mm"
include "crab.mm"
include "wss.mm"
include "w3a.mm"
include "citg.mm"
include "itgex.mm"
include "df-area.mm"
include "dmmpti.mm"
include "eleq2i.mm"
include "wceq.mm"
include "imaeq1.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "fveq2d.mm"
include "mpteq2dv.mm"
include "anbi12d.mm"
include "elrab.mm"
include "reex.mm"
include "xpex.mm"
include "elpw2.mm"
include "anbi1i.mm"
include "3anass.mm"
include "bitr4i.mm"
include "3bitri.mm"

theorem dmarea
  let vx: setvar x
  let cA: class A
  let vs: setvar s
  let vt: setvar t
  let vy: setvar y
  let cS: class S

  disjoint A x
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint A s
  disjoint t x
  disjoint t y
  disjoint A t
  disjoint x y
  disjoint A y
  disjoint S s
  disjoint S x
  assert |- ( A e. dom area <-> ( A C_ ( RR X. RR ) /\ A. x e. RR ( A " { x } ) e. ( `' vol " RR ) /\ ( x e. RR |-> ( vol ` ( A " { x } ) ) ) e. L^1 ) )

  proof
    cA
    carea
    cdm
    #
    wcel
    cA
    vt
    cv
    #
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
    #
    wcel
    #
    vx
    cr
    wral
    #
    vx
    cr
    @3
    cvol
    cfv
    #
    cmpt
    #
    cibl
    wcel
    #
    wa
    #
    vt
    cr
    cr
    cxp
    #
    cpw
    #
    crab
    #
    wcel
    cA
    @12
    wcel
    #
    cA
    @2
    cima
    #
    @4
    wcel
    #
    vx
    cr
    wral
    #
    vx
    cr
    @15
    cvol
    cfv
    #
    cmpt
    #
    cibl
    wcel
    #
    wa
    #
    wa
    #
    cA
    @11
    wss
    #
    @17
    @20
    w3a
    #
    @0
    @13
    cA
    vs
    @13
    vx
    cr
    vs
    cv
    @2
    cima
    cvol
    cfv
    #
    citg
    carea
    vx
    cr
    @25
    itgex
    vx
    vt
    vs
    df-area
    dmmpti
    eleq2i
    @10
    @21
    vt
    cA
    @12
    @1
    cA
    wceq
    #
    @6
    @17
    @9
    @20
    @26
    @5
    @16
    vx
    cr
    @26
    @3
    @15
    @4
    @1
    cA
    @2
    imaeq1
    #
    eleq1d
    ralbidv
    @26
    @8
    @19
    cibl
    @26
    vx
    cr
    @7
    @18
    @26
    @3
    @15
    cvol
    @27
    fveq2d
    mpteq2dv
    eleq1d
    anbi12d
    elrab
    @22
    @23
    @21
    wa
    @24
    @14
    @23
    @21
    cA
    @11
    cr
    cr
    reex
    reex
    xpex
    elpw2
    anbi1i
    @23
    @17
    @20
    3anass
    bitr4i
    3bitri
end
