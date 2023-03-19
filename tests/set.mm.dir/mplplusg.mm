include "cplusg.mm"
include "cfv.mm"
include "cbs.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "eqid.mm"
include "mplval2.mm"
include "ressplusg.mm"
include "ax-mp.mm"
include "eqtr4i.mm"

theorem mplplusg
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let cI: class I
  let cY: class Y
  assume mplplusg.y: |- Y = ( I mPoly R )
  assume mplplusg.s: |- S = ( I mPwSer R )
  assume mplplusg.p: |- .+ = ( +g ` Y )


  assert |- .+ = ( +g ` S )

  proof
    c.pl
    cY
    cplusg
    cfv
    #
    cS
    cplusg
    cfv
    #
    mplplusg.p
    cY
    cbs
    cfv
    #
    cvv
    wcel
    @1
    @0
    wceq
    cY
    cbs
    fvex
    @2
    @1
    cS
    cY
    cvv
    cY
    cR
    cS
    @2
    cI
    mplplusg.y
    mplplusg.s
    @2
    eqid
    mplval2
    @1
    eqid
    ressplusg
    ax-mp
    eqtr4i
end
