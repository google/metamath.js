include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "crg.mm"
include "cress.mm"
include "co.mm"
include "wa.mm"
include "cbs.mm"
include "wss.mm"
include "cur.mm"
include "eqid.mm"
include "issubrg.mm"
include "simplbi.mm"
include "simpld.mm"

theorem subrgrcl
  let cA: class A
  let cR: class R


  assert |- ( A e. ( SubRing ` R ) -> R e. Ring )

  proof
    cA
    cR
    csubrg
    cfv
    wcel
    #
    cR
    crg
    wcel
    #
    cR
    cA
    cress
    co
    crg
    wcel
    #
    @0
    @1
    @2
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
    @3
    cR
    @4
    @3
    eqid
    @4
    eqid
    issubrg
    simplbi
    simpld
end
