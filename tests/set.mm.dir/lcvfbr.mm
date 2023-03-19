include "clcv.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wpss.mm"
include "wrex.mm"
include "wn.mm"
include "copab.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "clss.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "rexeqdv.mm"
include "notbid.mm"
include "anbi2d.mm"
include "opabbidv.mm"
include "df-lcv.mm"
include "cxp.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpex.mm"
include "opabssxp.mm"
include "ssexi.mm"
include "fvmpt.mm"
include "3syl.mm"
include "syl5eq.mm"

theorem lcvfbr
  let wph: wff ph
  let vu: setvar u
  let vt: setvar t
  let cC: class C
  let cS: class S
  let cW: class W
  let cX: class X
  let vs: setvar s
  let vw: setvar w
  assume lcvfbr.s: |- S = ( LSubSp ` W )
  assume lcvfbr.c: |- C = ( <oL ` W )
  assume lcvfbr.w: |- ( ph -> W e. X )

  disjoint s t
  disjoint s u
  disjoint S s
  disjoint t u
  disjoint S t
  disjoint S u
  disjoint W s
  disjoint W t
  disjoint W u
  disjoint s w
  disjoint t w
  disjoint u w
  disjoint S w
  disjoint W w
  assert |- ( ph -> C = { <. t , u >. | ( ( t e. S /\ u e. S ) /\ ( t C. u /\ -. E. s e. S ( t C. s /\ s C. u ) ) ) } )

  proof
    wph
    cC
    cW
    clcv
    cfv
    #
    vt
    cv
    #
    cS
    wcel
    #
    vu
    cv
    #
    cS
    wcel
    #
    wa
    #
    @1
    @3
    wpss
    #
    @1
    vs
    cv
    #
    wpss
    @7
    @3
    wpss
    wa
    #
    vs
    cS
    wrex
    #
    wn
    #
    wa
    #
    wa
    #
    vt
    vu
    copab
    #
    lcvfbr.c
    wph
    cW
    cX
    wcel
    cW
    cvv
    wcel
    @0
    @13
    wceq
    lcvfbr.w
    cW
    cX
    elex
    vw
    cW
    @1
    vw
    cv
    #
    clss
    cfv
    #
    wcel
    #
    @3
    @15
    wcel
    #
    wa
    #
    @6
    @8
    vs
    @15
    wrex
    #
    wn
    #
    wa
    #
    wa
    #
    vt
    vu
    copab
    @13
    cvv
    clcv
    @14
    cW
    wceq
    #
    @22
    @12
    vt
    vu
    @23
    @18
    @5
    @21
    @11
    @23
    @16
    @2
    @17
    @4
    @23
    @15
    cS
    @1
    @23
    @15
    cW
    clss
    cfv
    #
    cS
    @14
    cW
    clss
    fveq2
    lcvfbr.s
    syl6eqr
    #
    eleq2d
    @23
    @15
    cS
    @3
    @25
    eleq2d
    anbi12d
    @23
    @20
    @10
    @6
    @23
    @19
    @9
    @23
    @8
    vs
    @15
    cS
    @25
    rexeqdv
    notbid
    anbi2d
    anbi12d
    opabbidv
    vw
    vu
    vt
    vs
    df-lcv
    @13
    cS
    cS
    cxp
    cS
    cS
    cS
    @24
    cvv
    lcvfbr.s
    cW
    clss
    fvex
    eqeltri
    #
    @26
    xpex
    @11
    vt
    vu
    cS
    cS
    opabssxp
    ssexi
    fvmpt
    3syl
    syl5eq
end
