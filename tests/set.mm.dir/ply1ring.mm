include "crg.mm"
include "wcel.mm"
include "c1o.mm"
include "cmpl.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "cps1.mm"
include "csubrg.mm"
include "eqid.mm"
include "ply1bas.mm"
include "ply1subrg.mm"
include "syl5eqelr.mm"
include "ply1val.mm"
include "subrgring.mm"
include "syl.mm"

theorem ply1ring
  let cP: class P
  let cR: class R
  assume ply1ring.p: |- P = ( Poly1 ` R )


  assert |- ( R e. Ring -> P e. Ring )

  proof
    cR
    crg
    wcel
    #
    c1o
    cR
    cmpl
    co
    cbs
    cfv
    #
    cR
    cps1
    cfv
    #
    csubrg
    cfv
    #
    wcel
    cP
    crg
    wcel
    @0
    @1
    cP
    cbs
    cfv
    #
    @3
    cP
    cR
    @2
    @4
    ply1ring.p
    @2
    eqid
    #
    @4
    eqid
    #
    ply1bas
    cP
    cR
    @2
    @4
    ply1ring.p
    @5
    @6
    ply1subrg
    syl5eqelr
    @1
    @2
    cP
    cP
    cR
    @2
    ply1ring.p
    @5
    ply1val
    subrgring
    syl
end
