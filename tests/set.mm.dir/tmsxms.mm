include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cds.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "ctopn.mm"
include "cmopn.mm"
include "wceq.mm"
include "cxme.mm"
include "wss.mm"
include "tmsds.mm"
include "tmsbas.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "ibi.mm"
include "ssid.mm"
include "xmetres2.mm"
include "sylancl.mm"
include "cxr.mm"
include "wf.mm"
include "wfn.mm"
include "xmetf.mm"
include "ffn.mm"
include "fnresdm.mm"
include "4syl.mm"
include "eqtr4d.mm"
include "eqid.mm"
include "tmstopn.mm"
include "eqtr2d.mm"
include "isxms2.mm"
include "sylanbrc.mm"

theorem tmsxms
  let cD: class D
  let cK: class K
  let cX: class X
  assume tmsbas.k: |- K = ( toMetSp ` D )


  assert |- ( D e. ( *Met ` X ) -> K e. *MetSp )

  proof
    cD
    cX
    cxmt
    cfv
    #
    wcel
    #
    cK
    cds
    cfv
    #
    cK
    cbs
    cfv
    #
    @3
    cxp
    #
    cres
    #
    @3
    cxmt
    cfv
    #
    wcel
    #
    cK
    ctopn
    cfv
    #
    @5
    cmopn
    cfv
    #
    wceq
    cK
    cxme
    wcel
    @1
    @2
    @6
    wcel
    #
    @3
    @3
    wss
    @7
    @1
    @10
    @1
    cD
    @2
    @0
    @6
    cD
    cK
    cX
    tmsbas.k
    tmsds
    #
    @1
    cX
    @3
    cxmt
    cD
    cK
    cX
    tmsbas.k
    tmsbas
    fveq2d
    eleq12d
    ibi
    #
    @3
    ssid
    @2
    @3
    @3
    xmetres2
    sylancl
    @1
    @9
    cD
    cmopn
    cfv
    #
    @8
    @1
    @5
    cD
    cmopn
    @1
    @5
    @2
    cD
    @1
    @10
    @4
    cxr
    @2
    wf
    @2
    @4
    wfn
    @5
    @2
    wceq
    @12
    @2
    @3
    xmetf
    @4
    cxr
    @2
    ffn
    @4
    @2
    fnresdm
    4syl
    @11
    eqtr4d
    fveq2d
    cD
    @13
    cK
    cX
    tmsbas.k
    @13
    eqid
    tmstopn
    eqtr2d
    @5
    @8
    cK
    @3
    @8
    eqid
    @3
    eqid
    @5
    eqid
    isxms2
    sylanbrc
end
