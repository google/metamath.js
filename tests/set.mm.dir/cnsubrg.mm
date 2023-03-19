include "ccnfld.mm"
include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "cr.mm"
include "wss.mm"
include "wa.mm"
include "cc.mm"
include "cpr.mm"
include "wceq.mm"
include "wo.mm"
include "cdif.mm"
include "c0.mm"
include "ssdif0.mm"
include "simpr.mm"
include "simplr.mm"
include "eqssd.mm"
include "orcd.mm"
include "sylan2br.mm"
include "wne.mm"
include "cv.mm"
include "wex.mm"
include "n0.mm"
include "simpll.mm"
include "cnfldbas.mm"
include "subrgss.mm"
include "syl.mm"
include "cre.mm"
include "ci.mm"
include "cim.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "replim.mm"
include "ad2antll.mm"
include "recl.mm"
include "sseldd.mm"
include "c1.mm"
include "cdiv.mm"
include "ax-icn.mm"
include "a1i.mm"
include "eldifi.mm"
include "adantl.mm"
include "imcl.mm"
include "recnd.mm"
include "wn.mm"
include "cc0.mm"
include "eldifn.mm"
include "wb.mm"
include "reim0b.mm"
include "necon3bbid.mm"
include "mpbid.mm"
include "divcan4d.mm"
include "mulcl.mm"
include "sylancr.mm"
include "divrecd.mm"
include "eqtr3d.mm"
include "cneg.mm"
include "cmin.mm"
include "recld.mm"
include "negsubd.mm"
include "oveq1d.mm"
include "pncan2d.mm"
include "3eqtrd.mm"
include "renegcld.mm"
include "cnfldadd.mm"
include "subrgacl.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"
include "rereccld.mm"
include "cnfldmul.mm"
include "subrgmcl.mm"
include "eqeltrd.mm"
include "adantrr.mm"
include "expr.mm"
include "ssrdv.mm"
include "olcd.mm"
include "ex.mm"
include "exlimdv.mm"
include "imp.mm"
include "sylan2b.mm"
include "pm2.61dane.mm"
include "elprg.mm"
include "adantr.mm"
include "mpbird.mm"

theorem cnsubrg
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( R e. ( SubRing ` CCfld ) /\ RR C_ R ) -> R e. { RR , CC } )

  proof
    cR
    ccnfld
    csubrg
    cfv
    #
    wcel
    #
    cr
    cR
    wss
    #
    wa
    #
    cR
    cr
    cc
    cpr
    wcel
    #
    cR
    cr
    wceq
    #
    cR
    cc
    wceq
    #
    wo
    #
    @3
    @7
    cR
    cr
    cdif
    #
    c0
    @8
    c0
    wceq
    @3
    cR
    cr
    wss
    #
    @7
    cR
    cr
    ssdif0
    @3
    @9
    wa
    #
    @5
    @6
    @10
    cR
    cr
    @3
    @9
    simpr
    @1
    @2
    @9
    simplr
    eqssd
    orcd
    sylan2br
    @8
    c0
    wne
    @3
    vx
    cv
    #
    @8
    wcel
    #
    vx
    wex
    #
    @7
    vx
    @8
    n0
    @3
    @13
    @7
    @3
    @12
    @7
    vx
    @3
    @12
    @7
    @3
    @12
    wa
    #
    @6
    @5
    @14
    cR
    cc
    @14
    @1
    cR
    cc
    wss
    @1
    @2
    @12
    simpll
    #
    cR
    cc
    ccnfld
    cnfldbas
    subrgss
    syl
    #
    @14
    vy
    cc
    cR
    @3
    @12
    vy
    cv
    #
    cc
    wcel
    #
    @17
    cR
    wcel
    @3
    @12
    @18
    wa
    #
    wa
    #
    @17
    @17
    cre
    cfv
    #
    ci
    @17
    cim
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    cR
    @18
    @17
    @24
    wceq
    @3
    @12
    @17
    replim
    ad2antll
    @20
    @1
    @21
    cR
    wcel
    @23
    cR
    wcel
    #
    @24
    cR
    wcel
    @1
    @2
    @19
    simpll
    #
    @20
    cr
    cR
    @21
    @1
    @2
    @19
    simplr
    #
    @18
    @21
    cr
    wcel
    @3
    @12
    @17
    recl
    ad2antll
    sseldd
    @20
    @1
    ci
    cR
    wcel
    #
    @22
    cR
    wcel
    @25
    @26
    @3
    @12
    @28
    @18
    @14
    ci
    ci
    @11
    cim
    cfv
    #
    cmul
    co
    #
    c1
    @29
    cdiv
    co
    #
    cmul
    co
    #
    cR
    @14
    @30
    @29
    cdiv
    co
    ci
    @32
    @14
    ci
    @29
    ci
    cc
    wcel
    #
    @14
    ax-icn
    a1i
    @14
    @29
    @14
    @11
    cc
    wcel
    #
    @29
    cr
    wcel
    @14
    cR
    cc
    @11
    @16
    @12
    @11
    cR
    wcel
    #
    @3
    @11
    cR
    cr
    eldifi
    adantl
    #
    sseldd
    #
    @11
    imcl
    syl
    #
    recnd
    #
    @14
    @11
    cr
    wcel
    #
    wn
    #
    @29
    cc0
    wne
    #
    @12
    @41
    @3
    @11
    cR
    cr
    eldifn
    adantl
    @14
    @34
    @41
    @42
    wb
    @37
    @34
    @40
    @29
    cc0
    @11
    reim0b
    necon3bbid
    syl
    mpbid
    #
    divcan4d
    @14
    @30
    @29
    @14
    @33
    @29
    cc
    wcel
    @30
    cc
    wcel
    ax-icn
    @39
    ci
    @29
    mulcl
    sylancr
    #
    @39
    @43
    divrecd
    eqtr3d
    @14
    @1
    @30
    cR
    wcel
    @31
    cR
    wcel
    @32
    cR
    wcel
    @15
    @14
    @11
    @11
    cre
    cfv
    #
    cneg
    #
    caddc
    co
    #
    @30
    cR
    @14
    @47
    @11
    @45
    cmin
    co
    @45
    @30
    caddc
    co
    #
    @45
    cmin
    co
    @30
    @14
    @11
    @45
    @37
    @14
    @45
    @14
    @11
    @37
    recld
    #
    recnd
    #
    negsubd
    @14
    @11
    @48
    @45
    cmin
    @14
    @34
    @11
    @48
    wceq
    @37
    @11
    replim
    syl
    oveq1d
    @14
    @45
    @30
    @50
    @44
    pncan2d
    3eqtrd
    @14
    @1
    @35
    @46
    cR
    wcel
    @47
    cR
    wcel
    @15
    @36
    @14
    cr
    cR
    @46
    @1
    @2
    @12
    simplr
    #
    @14
    @45
    @49
    renegcld
    sseldd
    cR
    caddc
    ccnfld
    @11
    @46
    cnfldadd
    subrgacl
    syl3anc
    eqeltrrd
    @14
    cr
    cR
    @31
    @51
    @14
    @29
    @38
    @43
    rereccld
    sseldd
    cR
    ccnfld
    cmul
    @30
    @31
    cnfldmul
    subrgmcl
    syl3anc
    eqeltrd
    adantrr
    @20
    cr
    cR
    @22
    @27
    @18
    @22
    cr
    wcel
    @3
    @12
    @17
    imcl
    ad2antll
    sseldd
    cR
    ccnfld
    cmul
    ci
    @22
    cnfldmul
    subrgmcl
    syl3anc
    cR
    caddc
    ccnfld
    @21
    @23
    cnfldadd
    subrgacl
    syl3anc
    eqeltrd
    expr
    ssrdv
    eqssd
    olcd
    ex
    exlimdv
    imp
    sylan2b
    pm2.61dane
    @1
    @4
    @7
    wb
    @2
    cR
    cr
    cc
    @0
    elprg
    adantr
    mpbird
end
