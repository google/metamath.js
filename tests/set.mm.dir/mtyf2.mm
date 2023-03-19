include "cmfs.mm"
include "wcel.mm"
include "cmcn.mm"
include "cfv.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wf.mm"
include "cmax.mm"
include "cmsta.mm"
include "wss.mm"
include "ccnv.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cfn.mm"
include "wn.mm"
include "cmvt.mm"
include "wral.mm"
include "wa.mm"
include "eqid.mm"
include "ismfs.mm"
include "ibi.mm"
include "simplrd.mm"

theorem mtyf2
  let cT: class T
  let cK: class K
  let cV: class V
  let cY: class Y
  let vv: setvar v
  assume mtyf2.v: |- V = ( mVR ` T )
  assume mvtf2.k: |- K = ( mTC ` T )
  assume mtyf2.y: |- Y = ( mType ` T )


  assert |- ( T e. mFS -> Y : V --> K )

  proof
    cT
    cmfs
    wcel
    #
    cT
    cmcn
    cfv
    #
    cV
    cin
    c0
    wceq
    #
    cV
    cK
    cY
    wf
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
    cY
    ccnv
    vv
    cv
    csn
    cima
    cfn
    wcel
    wn
    vv
    cT
    cmvt
    cfv
    #
    wral
    wa
    #
    @0
    @2
    @3
    wa
    @7
    wa
    vv
    @4
    @1
    @5
    cT
    @6
    cK
    cV
    cmfs
    cY
    @1
    eqid
    mtyf2.v
    mtyf2.y
    @6
    eqid
    mvtf2.k
    @4
    eqid
    @5
    eqid
    ismfs
    ibi
    simplrd
end
