include "cmfs.mm"
include "wcel.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cmtc.mm"
include "cfv.mm"
include "cmty.mm"
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
include "simplld.mm"

theorem mfsdisj
  let cC: class C
  let cT: class T
  let cV: class V
  let vv: setvar v
  assume mfsdisj.c: |- C = ( mCN ` T )
  assume mfsdisj.v: |- V = ( mVR ` T )


  assert |- ( T e. mFS -> ( C i^i V ) = (/) )

  proof
    cT
    cmfs
    wcel
    #
    cC
    cV
    cin
    c0
    wceq
    #
    cV
    cT
    cmtc
    cfv
    #
    cT
    cmty
    cfv
    #
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
    @3
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
    @1
    @4
    wa
    @8
    wa
    vv
    @5
    cC
    @6
    cT
    @7
    @2
    cV
    cmfs
    @3
    mfsdisj.c
    mfsdisj.v
    @3
    eqid
    @7
    eqid
    @2
    eqid
    @5
    eqid
    @6
    eqid
    ismfs
    ibi
    simplld
end
