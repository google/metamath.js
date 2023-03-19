include "wf.mm"
include "wfn.mm"
include "c0.mm"
include "wne.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "crn.mm"
include "wb.mm"
include "cnv.mm"
include "wcel.mm"
include "ffn.mm"
include "cn0v.mm"
include "cfv.mm"
include "eqid.mm"
include "nvzcl.mm"
include "ne0i.mm"
include "syl.mm"
include "fconst5.mm"
include "syl2anr.mm"

theorem nvo00
  let cT: class T
  let cU: class U
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume nvo00.1: |- X = ( BaseSet ` U )


  assert |- ( ( U e. NrmCVec /\ T : X --> Y ) -> ( T = ( X X. { Z } ) <-> ran T = { Z } ) )

  proof
    cX
    cY
    cT
    wf
    cT
    cX
    wfn
    cX
    c0
    wne
    #
    cT
    cX
    cZ
    csn
    #
    cxp
    wceq
    cT
    crn
    @1
    wceq
    wb
    cU
    cnv
    wcel
    #
    cX
    cY
    cT
    ffn
    @2
    cU
    cn0v
    cfv
    #
    cX
    wcel
    @0
    cU
    cX
    @3
    nvo00.1
    @3
    eqid
    nvzcl
    cX
    @3
    ne0i
    syl
    cX
    cZ
    cT
    fconst5
    syl2anr
end
