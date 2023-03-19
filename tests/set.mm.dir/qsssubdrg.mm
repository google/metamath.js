include "ccnfld.mm"
include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "cress.mm"
include "co.mm"
include "cdr.mm"
include "wa.mm"
include "cq.mm"
include "cv.mm"
include "cdiv.mm"
include "wceq.mm"
include "cn.mm"
include "wrex.mm"
include "cz.mm"
include "elq.mm"
include "cdvr.mm"
include "cbs.mm"
include "crg.mm"
include "cui.mm"
include "drngring.mm"
include "ad2antlr.mm"
include "wss.mm"
include "zsssubrg.mm"
include "ad2antrr.mm"
include "eqid.mm"
include "subrgbas.mm"
include "sseqtrd.mm"
include "simprl.mm"
include "sseldd.mm"
include "c0g.mm"
include "wne.mm"
include "nnz.mm"
include "ad2antll.mm"
include "cc0.mm"
include "nnne0.mm"
include "cnfld0.mm"
include "subrg0.mm"
include "neeqtrd.mm"
include "wb.mm"
include "drngunit.mm"
include "mpbir2and.mm"
include "dvrcl.mm"
include "syl3anc.mm"
include "simpll.mm"
include "cnflddiv.mm"
include "subrgdv.mm"
include "3eltr4d.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "syl5bi.mm"
include "ssrdv.mm"

theorem qsssubdrg
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( R e. ( SubRing ` CCfld ) /\ ( CCfld |`s R ) e. DivRing ) -> QQ C_ R )

  proof
    cR
    ccnfld
    csubrg
    cfv
    wcel
    #
    ccnfld
    cR
    cress
    co
    #
    cdr
    wcel
    #
    wa
    #
    vz
    cq
    cR
    vz
    cv
    #
    cq
    wcel
    @4
    vx
    cv
    #
    vy
    cv
    #
    cdiv
    co
    #
    wceq
    #
    vy
    cn
    wrex
    vx
    cz
    wrex
    @3
    @4
    cR
    wcel
    #
    vx
    vy
    @4
    elq
    @3
    @8
    @9
    vx
    vy
    cz
    cn
    @3
    @5
    cz
    wcel
    #
    @6
    cn
    wcel
    #
    wa
    #
    wa
    #
    @9
    @8
    @7
    cR
    wcel
    @13
    @5
    @6
    @1
    cdvr
    cfv
    #
    co
    #
    @1
    cbs
    cfv
    #
    @7
    cR
    @13
    @1
    crg
    wcel
    #
    @5
    @16
    wcel
    @6
    @1
    cui
    cfv
    #
    wcel
    #
    @15
    @16
    wcel
    @2
    @17
    @0
    @12
    @1
    drngring
    ad2antlr
    @13
    cz
    @16
    @5
    @13
    cz
    cR
    @16
    @0
    cz
    cR
    wss
    @2
    @12
    cR
    zsssubrg
    ad2antrr
    #
    @0
    cR
    @16
    wceq
    @2
    @12
    cR
    ccnfld
    @1
    @1
    eqid
    #
    subrgbas
    ad2antrr
    #
    sseqtrd
    #
    @3
    @10
    @11
    simprl
    #
    sseldd
    @13
    @19
    @6
    @16
    wcel
    #
    @6
    @1
    c0g
    cfv
    #
    wne
    #
    @13
    cz
    @16
    @6
    @23
    @11
    @6
    cz
    wcel
    @3
    @10
    @6
    nnz
    ad2antll
    sseldd
    @13
    @6
    cc0
    @26
    @11
    @6
    cc0
    wne
    @3
    @10
    @6
    nnne0
    ad2antll
    @0
    cc0
    @26
    wceq
    @2
    @12
    cR
    ccnfld
    @1
    cc0
    @21
    cnfld0
    subrg0
    ad2antrr
    neeqtrd
    @2
    @19
    @25
    @27
    wa
    wb
    @0
    @12
    @16
    @1
    @18
    @6
    @26
    @16
    eqid
    #
    @18
    eqid
    #
    @26
    eqid
    drngunit
    ad2antlr
    mpbir2and
    #
    @16
    @14
    @1
    @18
    @5
    @6
    @28
    @29
    @14
    eqid
    #
    dvrcl
    syl3anc
    @13
    @0
    @5
    cR
    wcel
    @19
    @7
    @15
    wceq
    @0
    @2
    @12
    simpll
    @13
    cz
    cR
    @5
    @20
    @24
    sseldd
    @30
    cR
    cdiv
    ccnfld
    @1
    @18
    @14
    @5
    @6
    @21
    cnflddiv
    @29
    @31
    subrgdv
    syl3anc
    @22
    3eltr4d
    @4
    @7
    cR
    eleq1
    syl5ibrcom
    rexlimdvva
    syl5bi
    ssrdv
end
