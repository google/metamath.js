include "cplusg.mm"
include "cfv.mm"
include "c1o.mm"
include "cmps.mm"
include "co.mm"
include "cps1.mm"
include "eqid.mm"
include "mplplusg.mm"
include "psr1plusg.mm"
include "cmpl.mm"
include "cbs.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "ply1val.mm"
include "ressplusg.mm"
include "ax-mp.mm"
include "3eqtr2i.mm"
include "eqtr4i.mm"

theorem ply1plusg
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let cY: class Y
  assume ply1plusg.y: |- Y = ( Poly1 ` R )
  assume ply1plusg.s: |- S = ( 1o mPoly R )
  assume ply1plusg.p: |- .+ = ( +g ` Y )


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
    ply1plusg.p
    @1
    c1o
    cR
    cmps
    co
    #
    cplusg
    cfv
    cR
    cps1
    cfv
    #
    cplusg
    cfv
    #
    @0
    @1
    cR
    @2
    c1o
    cS
    ply1plusg.s
    @2
    eqid
    #
    @1
    eqid
    mplplusg
    @4
    cR
    @2
    @3
    @3
    eqid
    #
    @5
    @4
    eqid
    #
    psr1plusg
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
    @4
    @3
    cY
    cvv
    cY
    cR
    @3
    ply1plusg.y
    @6
    ply1val
    @7
    ressplusg
    ax-mp
    3eqtr2i
    eqtr4i
end
