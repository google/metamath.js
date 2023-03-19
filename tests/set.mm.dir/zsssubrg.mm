include "ccnfld.mm"
include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "cv.mm"
include "wa.mm"
include "c1.mm"
include "cmg.mm"
include "co.mm"
include "cmul.mm"
include "cc.mm"
include "wceq.mm"
include "simpr.mm"
include "ax-1cn.mm"
include "cnfldmulg.mm"
include "sylancl.mm"
include "zcn.mm"
include "adantl.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "csubg.mm"
include "subrgsubg.mm"
include "adantr.mm"
include "cnfld1.mm"
include "subrg1cl.mm"
include "eqid.mm"
include "subgmulgcl.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "ssrdv.mm"

theorem zsssubrg
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( R e. ( SubRing ` CCfld ) -> ZZ C_ R )

  proof
    cR
    ccnfld
    csubrg
    cfv
    wcel
    #
    vx
    cz
    cR
    @0
    vx
    cv
    #
    cz
    wcel
    #
    @1
    cR
    wcel
    @0
    @2
    wa
    #
    @1
    c1
    ccnfld
    cmg
    cfv
    #
    co
    #
    @1
    cR
    @3
    @5
    @1
    c1
    cmul
    co
    #
    @1
    @3
    @2
    c1
    cc
    wcel
    @5
    @6
    wceq
    @0
    @2
    simpr
    #
    ax-1cn
    @1
    c1
    cnfldmulg
    sylancl
    @3
    @1
    @2
    @1
    cc
    wcel
    @0
    @1
    zcn
    adantl
    mulid1d
    eqtrd
    @3
    cR
    ccnfld
    csubg
    cfv
    wcel
    #
    @2
    c1
    cR
    wcel
    #
    @5
    cR
    wcel
    @0
    @8
    @2
    cR
    ccnfld
    subrgsubg
    adantr
    @7
    @0
    @9
    @2
    cR
    ccnfld
    c1
    cnfld1
    subrg1cl
    adantr
    cR
    @4
    ccnfld
    @1
    c1
    @4
    eqid
    subgmulgcl
    syl3anc
    eqeltrrd
    ex
    ssrdv
end
