include "ccrg.mm"
include "wcel.mm"
include "cps1.mm"
include "cfv.mm"
include "c1o.mm"
include "cmpl.mm"
include "co.mm"
include "cbs.mm"
include "csubrg.mm"
include "eqid.mm"
include "psr1crng.mm"
include "ply1bas.mm"
include "crg.mm"
include "crngring.mm"
include "ply1subrg.mm"
include "syl.mm"
include "syl5eqelr.mm"
include "ply1val.mm"
include "subrgcrng.mm"
include "syl2anc.mm"

theorem ply1crng
  let cP: class P
  let cR: class R
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  assume ply1val.1: |- P = ( Poly1 ` R )


  assert |- ( R e. CRing -> P e. CRing )

  proof
    cR
    ccrg
    wcel
    #
    cR
    cps1
    cfv
    #
    ccrg
    wcel
    c1o
    cR
    cmpl
    co
    cbs
    cfv
    #
    @1
    csubrg
    cfv
    #
    wcel
    cP
    ccrg
    wcel
    cR
    @1
    @1
    eqid
    #
    psr1crng
    @0
    @2
    cP
    cbs
    cfv
    #
    @3
    cP
    cR
    @1
    @5
    ply1val.1
    @4
    @5
    eqid
    #
    ply1bas
    @0
    cR
    crg
    wcel
    @5
    @3
    wcel
    cR
    crngring
    cP
    cR
    @1
    @5
    ply1val.1
    @4
    @6
    ply1subrg
    syl
    syl5eqelr
    @2
    @1
    cP
    cP
    cR
    @1
    ply1val.1
    @4
    ply1val
    subrgcrng
    syl2anc
end
