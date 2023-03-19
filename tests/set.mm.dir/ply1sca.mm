include "wcel.mm"
include "cps1.mm"
include "cfv.mm"
include "csca.mm"
include "eqid.mm"
include "psr1sca.mm"
include "c1o.mm"
include "cmpl.mm"
include "co.mm"
include "cbs.mm"
include "cvv.mm"
include "wceq.mm"
include "fvex.mm"
include "ply1val.mm"
include "resssca.mm"
include "ax-mp.mm"
include "syl6eq.mm"

theorem ply1sca
  let cP: class P
  let cR: class R
  let cV: class V
  assume ply1lmod.p: |- P = ( Poly1 ` R )


  assert |- ( R e. V -> R = ( Scalar ` P ) )

  proof
    cR
    cV
    wcel
    cR
    cR
    cps1
    cfv
    #
    csca
    cfv
    #
    cP
    csca
    cfv
    #
    @0
    cR
    cV
    @0
    eqid
    #
    psr1sca
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
    @1
    @2
    wceq
    @4
    cbs
    fvex
    @5
    @1
    @0
    cP
    cvv
    cP
    cR
    @0
    ply1lmod.p
    @3
    ply1val
    @1
    eqid
    resssca
    ax-mp
    syl6eq
end
