include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "cress.mm"
include "co.mm"
include "crg.mm"
include "wa.mm"
include "cbs.mm"
include "wss.mm"
include "cur.mm"
include "eqid.mm"
include "issubrg.mm"
include "simplbi.mm"
include "simprd.mm"
include "syl5eqel.mm"

theorem subrgring
  let cA: class A
  let cR: class R
  let cS: class S
  assume subrgring.1: |- S = ( R |`s A )


  assert |- ( A e. ( SubRing ` R ) -> S e. Ring )

  proof
    cA
    cR
    csubrg
    cfv
    wcel
    #
    cS
    cR
    cA
    cress
    co
    #
    crg
    subrgring.1
    @0
    cR
    crg
    wcel
    #
    @1
    crg
    wcel
    #
    @0
    @2
    @3
    wa
    cA
    cR
    cbs
    cfv
    #
    wss
    cR
    cur
    cfv
    #
    cA
    wcel
    wa
    cA
    @4
    cR
    @5
    @4
    eqid
    @5
    eqid
    issubrg
    simplbi
    simprd
    syl5eqel
end
