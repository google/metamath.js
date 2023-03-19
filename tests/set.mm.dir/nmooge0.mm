include "cnv.mm"
include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "cc0.mm"
include "cn0v.mm"
include "cfv.mm"
include "cnmcv.mm"
include "cxr.mm"
include "0xr.mm"
include "a1i.mm"
include "cr.mm"
include "simp2.mm"
include "eqid.mm"
include "nvzcl.mm"
include "ffvelrn.mm"
include "sylan2.mm"
include "ancoms.mm"
include "3adant2.mm"
include "nvcl.mm"
include "syl2anc.mm"
include "rexrd.mm"
include "nmoxr.mm"
include "cle.mm"
include "wbr.mm"
include "nvge0.mm"
include "cv.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cab.mm"
include "clt.mm"
include "csup.mm"
include "wss.mm"
include "nmosetre.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "nmosetn0.mm"
include "supxrub.mm"
include "syl2an.mm"
include "3impa.mm"
include "3comr.mm"
include "nmooval.mm"
include "breqtrrd.mm"
include "xrletrd.mm"

theorem nmooge0
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


  assert |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T : X --> Y ) -> 0 <_ ( N ` T ) )

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
    cc0
    cU
    cn0v
    cfv
    #
    cT
    cfv
    #
    cW
    cnmcv
    cfv
    #
    cfv
    #
    cT
    cN
    cfv
    #
    cc0
    cxr
    wcel
    @3
    0xr
    a1i
    @3
    @7
    @3
    @1
    @5
    cY
    wcel
    #
    @7
    cr
    wcel
    @0
    @1
    @2
    simp2
    #
    @0
    @2
    @9
    @1
    @2
    @0
    @9
    @0
    @2
    @4
    cX
    wcel
    @9
    cU
    cX
    @4
    nmoxr.1
    @4
    eqid
    #
    nvzcl
    cX
    cY
    @4
    cT
    ffvelrn
    sylan2
    ancoms
    3adant2
    #
    @5
    cW
    @6
    cY
    nmoxr.2
    @6
    eqid
    #
    nvcl
    syl2anc
    rexrd
    cT
    cU
    cN
    cW
    cX
    cY
    nmoxr.1
    nmoxr.2
    nmoxr.3
    nmoxr
    @3
    @1
    @9
    cc0
    @7
    cle
    wbr
    @10
    @12
    @5
    cW
    @6
    cY
    nmoxr.2
    @13
    nvge0
    syl2anc
    @3
    @7
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
    @14
    cT
    cfv
    @6
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
    @8
    cle
    @1
    @2
    @0
    @7
    @17
    cle
    wbr
    #
    @1
    @2
    @0
    @18
    @1
    @2
    wa
    #
    @16
    cxr
    wss
    @7
    @16
    wcel
    @18
    @0
    @19
    @16
    cr
    cxr
    vx
    vz
    cT
    @15
    @6
    cW
    cX
    cY
    nmoxr.2
    @13
    nmosetre
    ressxr
    syl6ss
    vx
    vz
    cT
    cU
    @15
    @6
    cX
    @4
    nmoxr.1
    @11
    @15
    eqid
    #
    nmosetn0
    @16
    @7
    supxrub
    syl2an
    3impa
    3comr
    vx
    vz
    cT
    cU
    @15
    @6
    cN
    cW
    cX
    cY
    nmoxr.1
    nmoxr.2
    @20
    @13
    nmoxr.3
    nmooval
    breqtrrd
    xrletrd
end
