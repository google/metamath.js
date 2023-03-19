include "cmfs.mm"
include "wcel.mm"
include "crn.mm"
include "wf.mm"
include "cmtc.mm"
include "cfv.mm"
include "wfo.mm"
include "eqid.mm"
include "mtyf2.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn4.mm"
include "sylib.mm"
include "fof.mm"
include "3syl.mm"
include "wceq.mm"
include "wb.mm"
include "mvtval.mm"
include "feq3.mm"
include "ax-mp.mm"
include "sylibr.mm"

theorem mtyf
  let cT: class T
  let cF: class F
  let cV: class V
  let cY: class Y
  assume mtyf.v: |- V = ( mVR ` T )
  assume mtyf.f: |- F = ( mVT ` T )
  assume mtyf.y: |- Y = ( mType ` T )


  assert |- ( T e. mFS -> Y : V --> F )

  proof
    cT
    cmfs
    wcel
    #
    cV
    cY
    crn
    #
    cY
    wf
    #
    cV
    cF
    cY
    wf
    #
    @0
    cV
    cT
    cmtc
    cfv
    #
    cY
    wf
    #
    cV
    @1
    cY
    wfo
    #
    @2
    cT
    @4
    cV
    cY
    mtyf.v
    @4
    eqid
    mtyf.y
    mtyf2
    @5
    cY
    cV
    wfn
    @6
    cV
    @4
    cY
    ffn
    cV
    cY
    dffn4
    sylib
    cV
    @1
    cY
    fof
    3syl
    cF
    @1
    wceq
    @3
    @2
    wb
    cT
    cF
    cY
    mtyf.f
    mtyf.y
    mvtval
    cF
    @1
    cV
    cY
    feq3
    ax-mp
    sylibr
end
