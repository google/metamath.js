include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "cur.mm"
include "crg.mm"
include "cress.mm"
include "co.mm"
include "wa.mm"
include "eqid.mm"
include "issubrg.mm"
include "simprbi.mm"
include "simpld.mm"

theorem subrgss
  let cA: class A
  let cB: class B
  let cR: class R
  assume subrgss.1: |- B = ( Base ` R )


  assert |- ( A e. ( SubRing ` R ) -> A C_ B )

  proof
    cA
    cR
    csubrg
    cfv
    wcel
    #
    cA
    cB
    wss
    #
    cR
    cur
    cfv
    #
    cA
    wcel
    #
    @0
    cR
    crg
    wcel
    cR
    cA
    cress
    co
    crg
    wcel
    wa
    @1
    @3
    wa
    cA
    cB
    cR
    @2
    subrgss.1
    @2
    eqid
    issubrg
    simprbi
    simpld
end
