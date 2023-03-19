include "cmulr.mm"
include "cfv.mm"
include "cbs.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "eqid.mm"
include "mplval2.mm"
include "ressmulr.mm"
include "ax-mp.mm"
include "eqtr4i.mm"

theorem mplmulr
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cI: class I
  let cY: class Y
  assume mplplusg.y: |- Y = ( I mPoly R )
  assume mplplusg.s: |- S = ( I mPwSer R )
  assume mplmulr.n: |- .x. = ( .r ` Y )


  assert |- .x. = ( .r ` S )

  proof
    c.x
    cY
    cmulr
    cfv
    #
    cS
    cmulr
    cfv
    #
    mplmulr.n
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
    cS
    cY
    @1
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
    ressmulr
    ax-mp
    eqtr4i
end
