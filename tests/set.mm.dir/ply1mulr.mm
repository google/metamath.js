include "cmulr.mm"
include "cfv.mm"
include "c1o.mm"
include "cmps.mm"
include "co.mm"
include "cps1.mm"
include "eqid.mm"
include "mplmulr.mm"
include "psr1mulr.mm"
include "cmpl.mm"
include "cbs.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "ply1val.mm"
include "ressmulr.mm"
include "ax-mp.mm"
include "3eqtr2i.mm"
include "eqtr4i.mm"

theorem ply1mulr
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cY: class Y
  assume ply1plusg.y: |- Y = ( Poly1 ` R )
  assume ply1plusg.s: |- S = ( 1o mPoly R )
  assume ply1mulr.n: |- .x. = ( .r ` Y )


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
    ply1mulr.n
    @1
    c1o
    cR
    cmps
    co
    #
    cmulr
    cfv
    cR
    cps1
    cfv
    #
    cmulr
    cfv
    #
    @0
    cR
    @2
    @1
    c1o
    cS
    ply1plusg.s
    @2
    eqid
    #
    @1
    eqid
    mplmulr
    cR
    @2
    @4
    @3
    @3
    eqid
    #
    @5
    @4
    eqid
    #
    psr1mulr
    c1o
    cR
    cmpl
    co
    #
    cbs
    cfv
    #
    cvv
    wcel
    @4
    @0
    wceq
    @8
    cbs
    fvex
    @9
    @3
    cY
    @4
    cvv
    cY
    cR
    @3
    ply1plusg.y
    @6
    ply1val
    @7
    ressmulr
    ax-mp
    3eqtr2i
    eqtr4i
end
