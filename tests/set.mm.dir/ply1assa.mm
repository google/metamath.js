include "ccrg.mm"
include "wcel.mm"
include "casa.mm"
include "cbs.mm"
include "cfv.mm"
include "cps1.mm"
include "csubrg.mm"
include "clss.mm"
include "crg.mm"
include "crngring.mm"
include "eqid.mm"
include "ply1subrg.mm"
include "syl.mm"
include "ply1lss.mm"
include "cur.mm"
include "wss.mm"
include "wa.mm"
include "wb.mm"
include "psr1assa.mm"
include "subrg1cl.mm"
include "subrgss.mm"
include "c1o.mm"
include "cmpl.mm"
include "co.mm"
include "cress.mm"
include "ply1val.mm"
include "ply1bas.mm"
include "oveq2i.mm"
include "eqtr4i.mm"
include "issubassa.mm"
include "syl3anc.mm"
include "mpbir2and.mm"

theorem ply1assa
  let cP: class P
  let cR: class R
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  assume ply1val.1: |- P = ( Poly1 ` R )


  assert |- ( R e. CRing -> P e. AssAlg )

  proof
    cR
    ccrg
    wcel
    #
    cP
    casa
    wcel
    #
    cP
    cbs
    cfv
    #
    cR
    cps1
    cfv
    #
    csubrg
    cfv
    wcel
    #
    @2
    @3
    clss
    cfv
    #
    wcel
    #
    @0
    cR
    crg
    wcel
    #
    @4
    cR
    crngring
    #
    cP
    cR
    @3
    @2
    ply1val.1
    @3
    eqid
    #
    @2
    eqid
    #
    ply1subrg
    syl
    #
    @0
    @7
    @6
    @8
    cP
    cR
    @3
    @2
    ply1val.1
    @9
    @10
    ply1lss
    syl
    @0
    @3
    casa
    wcel
    @3
    cur
    cfv
    #
    @2
    wcel
    #
    @2
    @3
    cbs
    cfv
    #
    wss
    #
    @1
    @4
    @6
    wa
    wb
    cR
    @3
    @9
    psr1assa
    @0
    @4
    @13
    @11
    @2
    @3
    @12
    @12
    eqid
    #
    subrg1cl
    syl
    @0
    @4
    @15
    @11
    @2
    @14
    @3
    @14
    eqid
    #
    subrgss
    syl
    @2
    cP
    @12
    @5
    @14
    @3
    cP
    @3
    c1o
    cR
    cmpl
    co
    cbs
    cfv
    #
    cress
    co
    @3
    @2
    cress
    co
    cP
    cR
    @3
    ply1val.1
    @9
    ply1val
    @2
    @18
    @3
    cress
    cP
    cR
    @3
    @2
    ply1val.1
    @9
    @10
    ply1bas
    oveq2i
    eqtr4i
    @5
    eqid
    @17
    @16
    issubassa
    syl3anc
    mpbir2and
end
