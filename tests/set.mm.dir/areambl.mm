include "carea.mm"
include "cdm.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "csn.mm"
include "cima.mm"
include "cvol.mm"
include "ccnv.mm"
include "cfv.mm"
include "cv.mm"
include "wral.mm"
include "cxp.mm"
include "wss.mm"
include "cmpt.mm"
include "cibl.mm"
include "dmarea.mm"
include "simp2bi.mm"
include "wceq.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "sylan.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "volf.mm"
include "ffn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "sylib.mm"

theorem areambl
  let cA: class A
  let cS: class S
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( S e. dom area /\ A e. RR ) -> ( ( S " { A } ) e. dom vol /\ ( vol ` ( S " { A } ) ) e. RR ) )

  proof
    cS
    carea
    cdm
    wcel
    #
    cA
    cr
    wcel
    #
    wa
    cS
    cA
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
    @3
    cvol
    cdm
    #
    wcel
    @3
    cvol
    cfv
    cr
    wcel
    wa
    #
    @0
    cS
    vx
    cv
    #
    csn
    #
    cima
    #
    @4
    wcel
    #
    vx
    cr
    wral
    #
    @1
    @5
    @0
    cS
    cr
    cr
    cxp
    wss
    @12
    vx
    cr
    @10
    cvol
    cfv
    cmpt
    cibl
    wcel
    vx
    cS
    dmarea
    simp2bi
    @11
    @5
    vx
    cA
    cr
    @8
    cA
    wceq
    #
    @10
    @3
    @4
    @13
    @9
    @2
    cS
    @8
    cA
    sneq
    imaeq2d
    eleq1d
    rspccva
    sylan
    @6
    cc0
    cpnf
    cicc
    co
    #
    cvol
    wf
    cvol
    @6
    wfn
    @5
    @7
    wb
    volf
    @6
    @14
    cvol
    ffn
    @6
    @3
    cr
    cvol
    elpreima
    mp2b
    sylib
end
