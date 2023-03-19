include "cmfs.mm"
include "wcel.mm"
include "ccnv.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cfn.mm"
include "wn.mm"
include "wral.mm"
include "cmcn.mm"
include "cfv.mm"
include "cmvar.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cmtc.mm"
include "wf.mm"
include "wa.mm"
include "cmax.mm"
include "cmsta.mm"
include "wss.mm"
include "eqid.mm"
include "ismfs.mm"
include "ibi.mm"
include "simprrd.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "eleq1d.mm"
include "notbid.mm"
include "rspccva.mm"
include "sylan.mm"

theorem mvtinf
  let cT: class T
  let cF: class F
  let cX: class X
  let cY: class Y
  let vv: setvar v
  assume mvtinf.f: |- F = ( mVT ` T )
  assume mvtinf.y: |- Y = ( mType ` T )


  assert |- ( ( T e. mFS /\ X e. F ) -> -. ( `' Y " { X } ) e. Fin )

  proof
    cT
    cmfs
    wcel
    #
    cY
    ccnv
    #
    vv
    cv
    #
    csn
    #
    cima
    #
    cfn
    wcel
    #
    wn
    #
    vv
    cF
    wral
    #
    cX
    cF
    wcel
    @1
    cX
    csn
    #
    cima
    #
    cfn
    wcel
    #
    wn
    #
    @0
    cT
    cmcn
    cfv
    #
    cT
    cmvar
    cfv
    #
    cin
    c0
    wceq
    @13
    cT
    cmtc
    cfv
    #
    cY
    wf
    wa
    #
    cT
    cmax
    cfv
    #
    cT
    cmsta
    cfv
    #
    wss
    #
    @7
    @0
    @15
    @18
    @7
    wa
    wa
    vv
    @16
    @12
    @17
    cT
    cF
    @14
    @13
    cmfs
    cY
    @12
    eqid
    @13
    eqid
    mvtinf.y
    mvtinf.f
    @14
    eqid
    @16
    eqid
    @17
    eqid
    ismfs
    ibi
    simprrd
    @6
    @11
    vv
    cX
    cF
    @2
    cX
    wceq
    #
    @5
    @10
    @19
    @4
    @9
    cfn
    @19
    @3
    @8
    @1
    @2
    cX
    sneq
    imaeq2d
    eleq1d
    notbid
    rspccva
    sylan
end
