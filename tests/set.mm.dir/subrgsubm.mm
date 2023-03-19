include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "csubmnd.mm"
include "cbs.mm"
include "wss.mm"
include "cur.mm"
include "cress.mm"
include "co.mm"
include "cmnd.mm"
include "eqid.mm"
include "subrgss.mm"
include "subrg1cl.mm"
include "cmgp.mm"
include "crg.mm"
include "wceq.mm"
include "subrgrcl.mm"
include "mgpress.mm"
include "mpancom.mm"
include "subrgring.mm"
include "ringmgp.mm"
include "syl.mm"
include "eqeltrd.mm"
include "w3a.mm"
include "wb.mm"
include "mgpbas.mm"
include "ringidval.mm"
include "issubm2.mm"
include "3syl.mm"
include "mpbir3and.mm"

theorem subrgsubm
  let cA: class A
  let cR: class R
  let cM: class M
  assume subrgsubm.1: |- M = ( mulGrp ` R )


  assert |- ( A e. ( SubRing ` R ) -> A e. ( SubMnd ` M ) )

  proof
    cA
    cR
    csubrg
    cfv
    #
    wcel
    #
    cA
    cM
    csubmnd
    cfv
    wcel
    #
    cA
    cR
    cbs
    cfv
    #
    wss
    #
    cR
    cur
    cfv
    #
    cA
    wcel
    #
    cM
    cA
    cress
    co
    #
    cmnd
    wcel
    #
    cA
    @3
    cR
    @3
    eqid
    #
    subrgss
    cA
    cR
    @5
    @5
    eqid
    #
    subrg1cl
    @1
    @7
    cR
    cA
    cress
    co
    #
    cmgp
    cfv
    #
    cmnd
    cR
    crg
    wcel
    #
    @1
    @7
    @12
    wceq
    cA
    cR
    subrgrcl
    #
    cA
    cR
    @11
    cM
    crg
    @0
    @11
    eqid
    #
    subrgsubm.1
    mgpress
    mpancom
    @1
    @11
    crg
    wcel
    @12
    cmnd
    wcel
    cA
    cR
    @11
    @15
    subrgring
    @11
    @12
    @12
    eqid
    ringmgp
    syl
    eqeltrd
    @1
    @13
    cM
    cmnd
    wcel
    @2
    @4
    @6
    @8
    w3a
    wb
    @14
    cR
    cM
    subrgsubm.1
    ringmgp
    @3
    cA
    @7
    cM
    @5
    @3
    cR
    cM
    subrgsubm.1
    @9
    mgpbas
    cR
    @5
    cM
    subrgsubm.1
    @10
    ringidval
    @7
    eqid
    issubm2
    3syl
    mpbir3and
end
