include "cnv.mm"
include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "cv.mm"
include "cnmcv.mm"
include "cfv.mm"
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
include "cr.mm"
include "cpnf.mm"
include "wne.mm"
include "wb.mm"
include "wss.mm"
include "c0.mm"
include "eqid.mm"
include "nmosetre.mm"
include "cn0v.mm"
include "nmosetn0.mm"
include "ne0i.mm"
include "syl.mm"
include "supxrre2.mm"
include "syl2anr.mm"
include "3impb.mm"
include "nmooval.mm"
include "eleq1d.mm"
include "neeq1d.mm"
include "3bitr4d.mm"

theorem nmorepnf
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


  assert |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T : X --> Y ) -> ( ( N ` T ) e. RR <-> ( N ` T ) =/= +oo ) )

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
    #
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
    @4
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
    cr
    wcel
    #
    @8
    cpnf
    wne
    #
    cT
    cN
    cfv
    #
    cr
    wcel
    @11
    cpnf
    wne
    @0
    @1
    @2
    @9
    @10
    wb
    #
    @1
    @2
    wa
    @7
    cr
    wss
    @7
    c0
    wne
    #
    @12
    @0
    vx
    vz
    cT
    @5
    @6
    cW
    cX
    cY
    nmoxr.2
    @6
    eqid
    #
    nmosetre
    @0
    cU
    cn0v
    cfv
    #
    cT
    cfv
    @6
    cfv
    #
    @7
    wcel
    @13
    vx
    vz
    cT
    cU
    @5
    @6
    cX
    @15
    nmoxr.1
    @15
    eqid
    @5
    eqid
    #
    nmosetn0
    @7
    @16
    ne0i
    syl
    @7
    supxrre2
    syl2anr
    3impb
    @3
    @11
    @8
    cr
    vx
    vz
    cT
    cU
    @5
    @6
    cN
    cW
    cX
    cY
    nmoxr.1
    nmoxr.2
    @17
    @14
    nmoxr.3
    nmooval
    #
    eleq1d
    @3
    @11
    @8
    cpnf
    @18
    neeq1d
    3bitr4d
end
