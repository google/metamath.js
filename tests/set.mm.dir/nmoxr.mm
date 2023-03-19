include "cnv.mm"
include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "cfv.mm"
include "cv.mm"
include "cnmcv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cab.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "eqid.mm"
include "nmooval.mm"
include "wss.mm"
include "cr.mm"
include "nmosetre.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "supxrcl.mm"
include "syl.mm"
include "3adant1.mm"
include "eqeltrd.mm"

theorem nmoxr
  let cT: class T
  let cU: class U
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vz: setvar z
  assume nmoxr.1: |- X = ( BaseSet ` U )
  assume nmoxr.2: |- Y = ( BaseSet ` W )
  assume nmoxr.3: |- N = ( U normOpOLD W )


  assert |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T : X --> Y ) -> ( N ` T ) e. RR* )

  proof
    cU
    cnv
    wcel
    #
    cW
    cnv
    wcel
    #
    cX
    cY
    cT
    wf
    #
    w3a
    cT
    cN
    cfv
    vz
    cv
    #
    cU
    cnmcv
    cfv
    #
    cfv
    c1
    cle
    wbr
    vx
    cv
    @3
    cT
    cfv
    cW
    cnmcv
    cfv
    #
    cfv
    wceq
    wa
    vz
    cX
    wrex
    vx
    cab
    #
    cxr
    clt
    csup
    #
    cxr
    vx
    vz
    cT
    cU
    @4
    @5
    cN
    cW
    cX
    cY
    nmoxr.1
    nmoxr.2
    @4
    eqid
    @5
    eqid
    #
    nmoxr.3
    nmooval
    @1
    @2
    @7
    cxr
    wcel
    #
    @0
    @1
    @2
    wa
    #
    @6
    cxr
    wss
    @9
    @10
    @6
    cr
    cxr
    vx
    vz
    cT
    @4
    @5
    cW
    cX
    cY
    nmoxr.2
    @8
    nmosetre
    ressxr
    syl6ss
    @6
    supxrcl
    syl
    3adant1
    eqeltrd
end
