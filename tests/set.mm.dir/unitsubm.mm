include "crg.mm"
include "wcel.mm"
include "csubmnd.mm"
include "cfv.mm"
include "cbs.mm"
include "wss.mm"
include "cur.mm"
include "cress.mm"
include "co.mm"
include "cmnd.mm"
include "eqid.mm"
include "unitss.mm"
include "a1i.mm"
include "1unit.mm"
include "cgrp.mm"
include "cmgp.mm"
include "oveq1i.mm"
include "unitgrp.mm"
include "grpmnd.mm"
include "syl.mm"
include "w3a.mm"
include "wb.mm"
include "ringmgp.mm"
include "mgpbas.mm"
include "ringidval.mm"
include "issubm2.mm"
include "mpbir3and.mm"

theorem unitsubm
  let cR: class R
  let cU: class U
  let cM: class M
  assume unitsubm.1: |- U = ( Unit ` R )
  assume unitsubm.2: |- M = ( mulGrp ` R )


  assert |- ( R e. Ring -> U e. ( SubMnd ` M ) )

  proof
    cR
    crg
    wcel
    #
    cU
    cM
    csubmnd
    cfv
    wcel
    #
    cU
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
    cU
    wcel
    #
    cM
    cU
    cress
    co
    #
    cmnd
    wcel
    #
    @3
    @0
    @2
    cR
    cU
    @2
    eqid
    #
    unitsubm.1
    unitss
    a1i
    cR
    cU
    @4
    unitsubm.1
    @4
    eqid
    #
    1unit
    @0
    @6
    cgrp
    wcel
    @7
    cR
    cU
    @6
    unitsubm.1
    cM
    cR
    cmgp
    cfv
    cU
    cress
    unitsubm.2
    oveq1i
    unitgrp
    @6
    grpmnd
    syl
    @0
    cM
    cmnd
    wcel
    @1
    @3
    @5
    @7
    w3a
    wb
    cR
    cM
    unitsubm.2
    ringmgp
    @2
    cU
    @6
    cM
    @4
    @2
    cR
    cM
    unitsubm.2
    @8
    mgpbas
    cR
    @4
    cM
    unitsubm.2
    @9
    ringidval
    @6
    eqid
    issubm2
    syl
    mpbir3and
end
