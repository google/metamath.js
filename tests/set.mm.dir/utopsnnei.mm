include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "csn.mm"
include "cima.mm"
include "cnei.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "eqid.mm"
include "imaeq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan2.mm"
include "3ad2ant2.mm"
include "cmpt.mm"
include "crn.mm"
include "utopsnneip.mm"
include "3adant2.mm"
include "eleq2d.mm"
include "wb.mm"
include "cvv.mm"
include "imaexg.mm"
include "elrnmpt.mm"
include "syl.mm"
include "bitrd.mm"
include "mpbird.mm"

theorem utopsnnei
  let cP: class P
  let cU: class U
  let cJ: class J
  let cV: class V
  let cX: class X
  let vp: setvar p
  let vv: setvar v
  let va: setvar a
  let vb: setvar b
  let vq: setvar q
  let vr: setvar r
  assume utoptop.1: |- J = ( unifTop ` U )


  assert |- ( ( U e. ( UnifOn ` X ) /\ V e. U /\ P e. X ) -> ( V " { P } ) e. ( ( nei ` J ) ` { P } ) )

  proof
    cU
    cX
    cust
    cfv
    wcel
    #
    cV
    cU
    wcel
    #
    cP
    cX
    wcel
    #
    w3a
    #
    cV
    cP
    csn
    #
    cima
    #
    @4
    cJ
    cnei
    cfv
    cfv
    #
    wcel
    #
    @5
    vv
    cv
    #
    @4
    cima
    #
    wceq
    #
    vv
    cU
    wrex
    #
    @1
    @0
    @11
    @2
    @1
    @5
    @5
    wceq
    #
    @11
    @5
    eqid
    @10
    @12
    vv
    cV
    cU
    @8
    cV
    wceq
    @9
    @5
    @5
    @8
    cV
    @4
    imaeq1
    eqeq2d
    rspcev
    mpan2
    3ad2ant2
    @3
    @7
    @5
    vv
    cU
    @9
    cmpt
    #
    crn
    #
    wcel
    #
    @11
    @3
    @6
    @14
    @5
    @0
    @2
    @6
    @14
    wceq
    @1
    vv
    cP
    cU
    cJ
    cX
    utoptop.1
    utopsnneip
    3adant2
    eleq2d
    @1
    @0
    @15
    @11
    wb
    #
    @2
    @1
    @5
    cvv
    wcel
    @16
    cV
    @4
    cU
    imaexg
    vv
    cU
    @9
    @5
    @13
    cvv
    @13
    eqid
    elrnmpt
    syl
    3ad2ant2
    bitrd
    mpbird
end
