include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cmpt.mm"
include "crn.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "cpw.mm"
include "crab.mm"
include "weq.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "cbvralv.mm"
include "eleq1.mm"
include "raleqbi1dv.mm"
include "syl5bb.mm"
include "cbvrabv.mm"
include "wa.mm"
include "simpl.mm"
include "sneqd.mm"
include "imaeq2d.mm"
include "mpteq2dva.mm"
include "rneqd.mm"
include "cbvmptv.mm"
include "utopsnneiplem.mm"

theorem utopsnneip
  let vv: setvar v
  let cP: class P
  let cU: class U
  let cJ: class J
  let cX: class X
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vq: setvar q
  let vr: setvar r
  assume utoptop.1: |- J = ( unifTop ` U )

  disjoint P v
  disjoint U v
  disjoint X v
  disjoint p v
  disjoint P p
  disjoint a b
  disjoint a p
  disjoint a q
  disjoint a r
  disjoint a v
  disjoint U a
  disjoint b p
  disjoint b q
  disjoint b r
  disjoint b v
  disjoint U b
  disjoint p q
  disjoint p r
  disjoint U p
  disjoint q r
  disjoint q v
  disjoint U q
  disjoint r v
  disjoint U r
  disjoint X a
  disjoint X b
  disjoint X p
  disjoint X q
  disjoint X r
  assert |- ( ( U e. ( UnifOn ` X ) /\ P e. X ) -> ( ( nei ` J ) ` { P } ) = ran ( v e. U |-> ( v " { P } ) ) )

  proof
    vv
    cP
    cU
    cJ
    vb
    cv
    #
    vr
    cv
    #
    vq
    cX
    vv
    cU
    vv
    cv
    #
    vq
    cv
    #
    csn
    #
    cima
    #
    cmpt
    #
    crn
    #
    cmpt
    #
    cfv
    #
    wcel
    #
    vr
    @0
    wral
    #
    vb
    cX
    cpw
    #
    crab
    @8
    cX
    vp
    va
    utoptop.1
    @11
    va
    cv
    #
    vp
    cv
    #
    @8
    cfv
    #
    wcel
    #
    vp
    @13
    wral
    #
    vb
    va
    @12
    @11
    @0
    @15
    wcel
    #
    vp
    @0
    wral
    vb
    va
    weq
    @17
    @10
    @18
    vr
    vp
    @0
    vr
    vp
    weq
    @9
    @15
    @0
    @1
    @14
    @8
    fveq2
    eleq2d
    cbvralv
    @18
    @16
    vp
    @0
    @13
    @0
    @13
    @15
    eleq1
    raleqbi1dv
    syl5bb
    cbvrabv
    vq
    vp
    cX
    @7
    vv
    cU
    @2
    @14
    csn
    #
    cima
    #
    cmpt
    #
    crn
    vq
    vp
    weq
    #
    @6
    @21
    @22
    vv
    cU
    @5
    @20
    @22
    @2
    cU
    wcel
    #
    wa
    #
    @4
    @19
    @2
    @24
    @3
    @14
    @22
    @23
    simpl
    sneqd
    imaeq2d
    mpteq2dva
    rneqd
    cbvmptv
    utopsnneiplem
end
