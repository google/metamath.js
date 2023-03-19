include "wcel.mm"
include "cfv.mm"
include "c2nd.mm"
include "crn.mm"
include "cin.mm"
include "cpw.mm"
include "cfn.mm"
include "mvrsval.mm"
include "wss.mm"
include "inss2.mm"
include "a1i.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "wfo.mm"
include "fzofi.mm"
include "wfn.mm"
include "cmcn.mm"
include "cun.mm"
include "cword.mm"
include "wf.mm"
include "cmtc.mm"
include "cxp.mm"
include "xp2nd.mm"
include "eqid.mm"
include "mexval2.mm"
include "eleq2s.mm"
include "wrdf.mm"
include "ffn.mm"
include "3syl.mm"
include "dffn4.mm"
include "sylib.mm"
include "fofi.mm"
include "sylancr.mm"
include "inss1.mm"
include "ssfi.mm"
include "sylancl.mm"
include "elfpw.mm"
include "sylanbrc.mm"
include "eqeltrd.mm"

theorem mvrsfpw
  let cT: class T
  let cE: class E
  let cV: class V
  let cW: class W
  let cX: class X
  let ve: setvar e
  let vt: setvar t
  assume mvrsval.v: |- V = ( mVR ` T )
  assume mvrsval.e: |- E = ( mEx ` T )
  assume mvrsval.w: |- W = ( mVars ` T )


  assert |- ( X e. E -> ( W ` X ) e. ( ~P V i^i Fin ) )

  proof
    cX
    cE
    wcel
    #
    cX
    cW
    cfv
    cX
    c2nd
    cfv
    #
    crn
    #
    cV
    cin
    #
    cV
    cpw
    cfn
    cin
    #
    cT
    cE
    cV
    cW
    cX
    mvrsval.v
    mvrsval.e
    mvrsval.w
    mvrsval
    @0
    @3
    cV
    wss
    #
    @3
    cfn
    wcel
    #
    @3
    @4
    wcel
    @5
    @0
    @2
    cV
    inss2
    a1i
    @0
    @2
    cfn
    wcel
    #
    @3
    @2
    wss
    @6
    @0
    cc0
    @1
    chash
    cfv
    #
    cfzo
    co
    #
    cfn
    wcel
    @9
    @2
    @1
    wfo
    #
    @7
    cc0
    @8
    fzofi
    @0
    @1
    @9
    wfn
    #
    @10
    @0
    @1
    cT
    cmcn
    cfv
    #
    cV
    cun
    #
    cword
    #
    wcel
    #
    @9
    @13
    @1
    wf
    @11
    @15
    cX
    cT
    cmtc
    cfv
    #
    @14
    cxp
    cE
    cX
    @16
    @14
    xp2nd
    @12
    cT
    cE
    @16
    cV
    @16
    eqid
    mvrsval.e
    @12
    eqid
    mvrsval.v
    mexval2
    eleq2s
    @13
    @1
    wrdf
    @9
    @13
    @1
    ffn
    3syl
    @9
    @1
    dffn4
    sylib
    @9
    @2
    @1
    fofi
    sylancr
    @2
    cV
    inss1
    @2
    @3
    ssfi
    sylancl
    @3
    cV
    elfpw
    sylanbrc
    eqeltrd
end
