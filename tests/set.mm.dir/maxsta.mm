include "cmfs.mm"
include "wcel.mm"
include "cmcn.mm"
include "cfv.mm"
include "cmvar.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cmtc.mm"
include "cmty.mm"
include "wf.mm"
include "wa.mm"
include "wss.mm"
include "ccnv.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cfn.mm"
include "wn.mm"
include "cmvt.mm"
include "wral.mm"
include "eqid.mm"
include "ismfs.mm"
include "ibi.mm"
include "simprld.mm"

theorem maxsta
  let cA: class A
  let cS: class S
  let cT: class T
  let vv: setvar v
  assume maxsta.a: |- A = ( mAx ` T )
  assume maxsta.s: |- S = ( mStat ` T )


  assert |- ( T e. mFS -> A C_ S )

  proof
    cT
    cmfs
    wcel
    #
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
    @2
    cT
    cmtc
    cfv
    #
    cT
    cmty
    cfv
    #
    wf
    wa
    #
    cA
    cS
    wss
    #
    @4
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
    #
    @0
    @5
    @6
    @8
    wa
    wa
    vv
    cA
    @1
    cS
    cT
    @7
    @3
    @2
    cmfs
    @4
    @1
    eqid
    @2
    eqid
    @4
    eqid
    @7
    eqid
    @3
    eqid
    maxsta.a
    maxsta.s
    ismfs
    ibi
    simprld
end
