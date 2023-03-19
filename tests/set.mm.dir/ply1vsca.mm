include "cvsca.mm"
include "cfv.mm"
include "c1o.mm"
include "cmps.mm"
include "co.mm"
include "cps1.mm"
include "eqid.mm"
include "mplvsca2.mm"
include "psr1vsca.mm"
include "cmpl.mm"
include "cbs.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "ply1val.mm"
include "ressvsca.mm"
include "ax-mp.mm"
include "3eqtr2i.mm"
include "eqtr4i.mm"

theorem ply1vsca
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cY: class Y
  assume ply1plusg.y: |- Y = ( Poly1 ` R )
  assume ply1plusg.s: |- S = ( 1o mPoly R )
  assume ply1vscafval.n: |- .x. = ( .s ` Y )


  assert |- .x. = ( .s ` S )

  proof
    c.x
    cY
    cvsca
    cfv
    #
    cS
    cvsca
    cfv
    #
    ply1vscafval.n
    @1
    c1o
    cR
    cmps
    co
    #
    cvsca
    cfv
    cR
    cps1
    cfv
    #
    cvsca
    cfv
    #
    @0
    cS
    cR
    @2
    @1
    c1o
    ply1plusg.s
    @2
    eqid
    #
    @1
    eqid
    mplvsca2
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
    psr1vsca
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
    ressvsca
    ax-mp
    3eqtr2i
    eqtr4i
end
