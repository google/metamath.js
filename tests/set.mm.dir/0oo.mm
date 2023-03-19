include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "cn0v.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "wss.mm"
include "fvex.mm"
include "fconst.mm"
include "eqid.mm"
include "nvzcl.mm"
include "snssd.mm"
include "fss.mm"
include "sylancr.mm"
include "adantl.mm"
include "0ofval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem 0oo
  let cU: class U
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume 0oo.1: |- X = ( BaseSet ` U )
  assume 0oo.2: |- Y = ( BaseSet ` W )
  assume 0oo.0: |- Z = ( U 0op W )


  assert |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> Z : X --> Y )

  proof
    cU
    cnv
    wcel
    #
    cW
    cnv
    wcel
    #
    wa
    #
    cX
    cY
    cZ
    wf
    cX
    cY
    cX
    cW
    cn0v
    cfv
    #
    csn
    #
    cxp
    #
    wf
    #
    @1
    @6
    @0
    @1
    cX
    @4
    @5
    wf
    @4
    cY
    wss
    @6
    cX
    @3
    cW
    cn0v
    fvex
    fconst
    @1
    @3
    cY
    cW
    cY
    @3
    0oo.2
    @3
    eqid
    #
    nvzcl
    snssd
    cX
    @4
    cY
    @5
    fss
    sylancr
    adantl
    @2
    cX
    cY
    cZ
    @5
    cU
    cZ
    cW
    cX
    @3
    0oo.1
    @7
    0oo.0
    0ofval
    feq1d
    mpbird
end
