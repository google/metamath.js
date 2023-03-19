include "cv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "breq1.mm"
include "mplbas.mm"
include "elrab2.mm"

theorem mplelbas
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cU: class U
  let cI: class I
  let cX: class X
  let c.0: class .0.
  let vf: setvar f
  let vi: setvar i
  let vr: setvar r
  let vs: setvar s
  assume mplval.p: |- P = ( I mPoly R )
  assume mplval.s: |- S = ( I mPwSer R )
  assume mplval.b: |- B = ( Base ` S )
  assume mplval.z: |- .0. = ( 0g ` R )
  assume mplbas.u: |- U = ( Base ` P )


  assert |- ( X e. U <-> ( X e. B /\ X finSupp .0. ) )

  proof
    vf
    cv
    #
    c.0
    cfsupp
    wbr
    cX
    c.0
    cfsupp
    wbr
    vf
    cX
    cB
    cU
    @0
    cX
    c.0
    cfsupp
    breq1
    cB
    cP
    cR
    cS
    cU
    vf
    cI
    c.0
    mplval.p
    mplval.s
    mplval.b
    mplval.z
    mplbas.u
    mplbas
    elrab2
end
