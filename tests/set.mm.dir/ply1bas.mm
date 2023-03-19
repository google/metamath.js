include "cbs.mm"
include "cfv.mm"
include "c1o.mm"
include "cmpl.mm"
include "co.mm"
include "wss.mm"
include "wceq.mm"
include "cmps.mm"
include "eqid.mm"
include "psr1bas2.mm"
include "mplbasss.mm"
include "ply1val.mm"
include "ressbas2.mm"
include "ax-mp.mm"
include "eqtr4i.mm"

theorem ply1bas
  let cP: class P
  let cR: class R
  let cS: class S
  let cU: class U
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume ply1val.1: |- P = ( Poly1 ` R )
  assume ply1val.2: |- S = ( PwSer1 ` R )
  assume ply1bas.u: |- U = ( Base ` P )


  assert |- U = ( Base ` ( 1o mPoly R ) )

  proof
    cU
    cP
    cbs
    cfv
    #
    c1o
    cR
    cmpl
    co
    #
    cbs
    cfv
    #
    ply1bas.u
    @2
    cS
    cbs
    cfv
    #
    wss
    @2
    @0
    wceq
    @3
    @1
    cR
    c1o
    cR
    cmps
    co
    #
    @2
    c1o
    @1
    eqid
    @4
    eqid
    #
    @2
    eqid
    @3
    cR
    cS
    @4
    ply1val.2
    @3
    eqid
    #
    @5
    psr1bas2
    mplbasss
    @2
    @3
    cP
    cS
    cP
    cR
    cS
    ply1val.1
    ply1val.2
    ply1val
    @6
    ressbas2
    ax-mp
    eqtr4i
end
