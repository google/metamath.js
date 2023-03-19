include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "wa.mm"
include "0ofval.mm"
include "fveq1d.mm"
include "3adant3.mm"
include "cn0v.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fvconst2.mm"
include "3ad2ant3.mm"
include "eqtrd.mm"

theorem 0oval
  let cA: class A
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


  assert |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ A e. X ) -> ( O ` A ) = Z )

  proof
    cU
    cnv
    wcel
    #
    cW
    cnv
    wcel
    #
    cA
    cX
    wcel
    #
    w3a
    cA
    cO
    cfv
    #
    cA
    cX
    cZ
    csn
    cxp
    #
    cfv
    #
    cZ
    @0
    @1
    @3
    @5
    wceq
    @2
    @0
    @1
    wa
    cA
    cO
    @4
    cU
    cO
    cW
    cX
    cZ
    0oval.1
    0oval.6
    0oval.0
    0ofval
    fveq1d
    3adant3
    @2
    @0
    @5
    cZ
    wceq
    @1
    cX
    cZ
    cA
    cZ
    cW
    cn0v
    cfv
    cvv
    0oval.6
    cW
    cn0v
    fvex
    eqeltri
    fvconst2
    3ad2ant3
    eqtrd
end
