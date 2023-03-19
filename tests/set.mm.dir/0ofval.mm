include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "c0o.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "cv.mm"
include "cba.mm"
include "cfv.mm"
include "cn0v.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "xpeq1d.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "df-0o.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "snex.mm"
include "xpex.mm"
include "ovmpt2.mm"
include "syl5eq.mm"

theorem 0ofval
  let cU: class U
  let cO: class O
  let cW: class W
  let cX: class X
  let cZ: class Z
  let vu: setvar u
  let vw: setvar w
  assume 0oval.1: |- X = ( BaseSet ` U )
  assume 0oval.6: |- Z = ( 0vec ` W )
  assume 0oval.0: |- O = ( U 0op W )


  assert |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> O = ( X X. { Z } ) )

  proof
    cU
    cnv
    wcel
    cW
    cnv
    wcel
    wa
    cO
    cU
    cW
    c0o
    co
    cX
    cZ
    csn
    #
    cxp
    #
    0oval.0
    vu
    vw
    cU
    cW
    cnv
    cnv
    vu
    cv
    #
    cba
    cfv
    #
    vw
    cv
    #
    cn0v
    cfv
    #
    csn
    #
    cxp
    @1
    c0o
    cX
    @6
    cxp
    @2
    cU
    wceq
    #
    @3
    cX
    @6
    @7
    @3
    cU
    cba
    cfv
    #
    cX
    @2
    cU
    cba
    fveq2
    0oval.1
    syl6eqr
    xpeq1d
    @4
    cW
    wceq
    #
    @6
    @0
    cX
    @9
    @5
    cZ
    @9
    @5
    cW
    cn0v
    cfv
    cZ
    @4
    cW
    cn0v
    fveq2
    0oval.6
    syl6eqr
    sneqd
    xpeq2d
    vw
    vu
    df-0o
    cX
    @0
    cX
    @8
    cvv
    0oval.1
    cU
    cba
    fvex
    eqeltri
    cZ
    snex
    xpex
    ovmpt2
    syl5eq
end
