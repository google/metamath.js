include "cv.mm"
include "c0g.mm"
include "cfv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "crab.mm"
include "eqid.mm"
include "mplbas.mm"
include "ssrab2.mm"
include "eqsstri.mm"

theorem mplbasss
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cU: class U
  let cI: class I
  let vf: setvar f
  assume mplval2.p: |- P = ( I mPoly R )
  assume mplval2.s: |- S = ( I mPwSer R )
  assume mplval2.u: |- U = ( Base ` P )
  assume mplbasss.b: |- B = ( Base ` S )


  assert |- U C_ B

  proof
    cU
    vf
    cv
    cR
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    vf
    cB
    crab
    cB
    cB
    cP
    cR
    cS
    cU
    vf
    cI
    @0
    mplval2.p
    mplval2.s
    mplbasss.b
    @0
    eqid
    mplval2.u
    mplbas
    @1
    vf
    cB
    ssrab2
    eqsstri
end
