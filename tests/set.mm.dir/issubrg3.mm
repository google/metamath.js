include "crg.mm"
include "wcel.mm"
include "csubrg.mm"
include "cfv.mm"
include "csubg.mm"
include "cur.mm"
include "cv.mm"
include "cmulr.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "csubmnd.mm"
include "w3a.mm"
include "cbs.mm"
include "eqid.mm"
include "issubrg2.mm"
include "3anass.mm"
include "syl6bb.mm"
include "cmnd.mm"
include "wss.mm"
include "wb.mm"
include "ringmgp.mm"
include "subgss.mm"
include "mgpbas.mm"
include "ringidval.mm"
include "mgpplusg.mm"
include "issubm.mm"
include "baibd.mm"
include "syl2an.mm"
include "pm5.32da.mm"
include "bitr4d.mm"

theorem issubrg3
  let cR: class R
  let cS: class S
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  assume issubrg3.m: |- M = ( mulGrp ` R )


  assert |- ( R e. Ring -> ( S e. ( SubRing ` R ) <-> ( S e. ( SubGrp ` R ) /\ S e. ( SubMnd ` M ) ) ) )

  proof
    cR
    crg
    wcel
    #
    cS
    cR
    csubrg
    cfv
    wcel
    #
    cS
    cR
    csubg
    cfv
    wcel
    #
    cR
    cur
    cfv
    #
    cS
    wcel
    #
    vx
    cv
    vy
    cv
    cR
    cmulr
    cfv
    #
    co
    cS
    wcel
    vy
    cS
    wral
    vx
    cS
    wral
    #
    wa
    #
    wa
    #
    @2
    cS
    cM
    csubmnd
    cfv
    wcel
    #
    wa
    @0
    @1
    @2
    @4
    @6
    w3a
    @8
    vx
    vy
    cS
    cR
    cbs
    cfv
    #
    cR
    @5
    @3
    @10
    eqid
    #
    @3
    eqid
    #
    @5
    eqid
    #
    issubrg2
    @2
    @4
    @6
    3anass
    syl6bb
    @0
    @2
    @9
    @7
    @0
    cM
    cmnd
    wcel
    #
    cS
    @10
    wss
    #
    @9
    @7
    wb
    @2
    cR
    cM
    issubrg3.m
    ringmgp
    @10
    cS
    cR
    @11
    subgss
    @14
    @9
    @15
    @7
    @14
    @9
    @15
    @4
    @6
    w3a
    @15
    @7
    wa
    vx
    vy
    @10
    @5
    cS
    cM
    @3
    @10
    cR
    cM
    issubrg3.m
    @11
    mgpbas
    cR
    @3
    cM
    issubrg3.m
    @12
    ringidval
    cR
    @5
    cM
    issubrg3.m
    @13
    mgpplusg
    issubm
    @15
    @4
    @6
    3anass
    syl6bb
    baibd
    syl2an
    pm5.32da
    bitr4d
end
