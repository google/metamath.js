include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c3.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cs3.mm"
include "wrex.mm"
include "cc0.mm"
include "c1.mm"
include "c2.mm"
include "w3a.mm"
include "cfzo.mm"
include "co.mm"
include "ctp.mm"
include "c0ex.mm"
include "tpid1.mm"
include "fzo0to3tp.mm"
include "eleqtrri.mm"
include "oveq2.mm"
include "syl5eleqr.mm"
include "wrdsymbcl.mm"
include "sylan2.mm"
include "1ex.mm"
include "tpid2.mm"
include "2ex.mm"
include "tpid3.mm"
include "simpr.mm"
include "eqid.mm"
include "3pm3.2i.mm"
include "jctir.mm"
include "eqeq2.mm"
include "3anbi1d.mm"
include "anbi2d.mm"
include "3anbi2d.mm"
include "3anbi3d.mm"
include "rspc3ev.mm"
include "syl31anc.mm"
include "wb.mm"
include "wi.mm"
include "df-3an.mm"
include "eqwrds3.mm"
include "ex.mm"
include "syl5bir.mm"
include "expd.mm"
include "adantr.mm"
include "imp31.mm"
include "rexbidva.mm"
include "2rexbidva.mm"
include "mpbird.mm"
include "s3cl.mm"
include "ad4ant123.mm"
include "s3len.mm"
include "eleq1.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "adantl.mm"
include "rexlimdva.mm"
include "rexlimivv.mm"
include "impbii.mm"

theorem wrdl3s3
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vc: setvar c

  disjoint V a
  disjoint V b
  disjoint V c
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint W a
  disjoint W b
  disjoint W c
  assert |- ( ( W e. Word V /\ ( # ` W ) = 3 ) <-> E. a e. V E. b e. V E. c e. V W = <" a b c "> )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cW
    chash
    cfv
    #
    c3
    wceq
    #
    wa
    #
    cW
    va
    cv
    #
    vb
    cv
    #
    vc
    cv
    #
    cs3
    #
    wceq
    #
    vc
    cV
    wrex
    #
    vb
    cV
    wrex
    va
    cV
    wrex
    #
    @4
    @11
    @3
    cc0
    cW
    cfv
    #
    @5
    wceq
    #
    c1
    cW
    cfv
    #
    @6
    wceq
    #
    c2
    cW
    cfv
    #
    @7
    wceq
    #
    w3a
    #
    wa
    #
    vc
    cV
    wrex
    #
    vb
    cV
    wrex
    va
    cV
    wrex
    #
    @4
    @12
    cV
    wcel
    #
    @14
    cV
    wcel
    #
    @16
    cV
    wcel
    #
    @3
    @12
    @12
    wceq
    #
    @14
    @14
    wceq
    #
    @16
    @16
    wceq
    #
    w3a
    #
    wa
    #
    @21
    @3
    @1
    cc0
    cc0
    @2
    cfzo
    co
    #
    wcel
    @22
    @3
    cc0
    cc0
    c3
    cfzo
    co
    #
    @30
    cc0
    cc0
    c1
    c2
    ctp
    #
    @31
    cc0
    c1
    c2
    c0ex
    tpid1
    fzo0to3tp
    eleqtrri
    @2
    c3
    cc0
    cfzo
    oveq2
    #
    syl5eleqr
    cc0
    cV
    cW
    wrdsymbcl
    sylan2
    @3
    @1
    c1
    @30
    wcel
    @23
    @3
    c1
    @31
    @30
    c1
    @32
    @31
    cc0
    c1
    c2
    1ex
    tpid2
    fzo0to3tp
    eleqtrri
    @33
    syl5eleqr
    c1
    cV
    cW
    wrdsymbcl
    sylan2
    @3
    @1
    c2
    @30
    wcel
    @24
    @3
    c2
    @31
    @30
    c2
    @32
    @31
    cc0
    c1
    c2
    2ex
    tpid3
    fzo0to3tp
    eleqtrri
    @33
    syl5eleqr
    c2
    cV
    cW
    wrdsymbcl
    sylan2
    @4
    @3
    @28
    @1
    @3
    simpr
    @25
    @26
    @27
    @12
    eqid
    @14
    eqid
    @16
    eqid
    3pm3.2i
    jctir
    @19
    @29
    @3
    @25
    @15
    @17
    w3a
    #
    wa
    @3
    @25
    @26
    @17
    w3a
    #
    wa
    va
    vb
    vc
    @12
    @14
    @16
    cV
    cV
    cV
    @5
    @12
    wceq
    #
    @18
    @34
    @3
    @36
    @13
    @25
    @15
    @17
    @5
    @12
    @12
    eqeq2
    3anbi1d
    anbi2d
    @6
    @14
    wceq
    #
    @34
    @35
    @3
    @37
    @15
    @26
    @25
    @17
    @6
    @14
    @14
    eqeq2
    3anbi2d
    anbi2d
    @7
    @16
    wceq
    #
    @35
    @28
    @3
    @38
    @17
    @27
    @25
    @26
    @7
    @16
    @16
    eqeq2
    3anbi3d
    anbi2d
    rspc3ev
    syl31anc
    @4
    @10
    @20
    va
    vb
    cV
    cV
    @4
    @5
    cV
    wcel
    #
    @6
    cV
    wcel
    #
    wa
    #
    wa
    @9
    @19
    vc
    cV
    @4
    @41
    @7
    cV
    wcel
    #
    @9
    @19
    wb
    #
    @1
    @41
    @42
    @43
    wi
    wi
    @3
    @1
    @41
    @42
    @43
    @41
    @42
    wa
    #
    @39
    @40
    @42
    w3a
    #
    @1
    @43
    @39
    @40
    @42
    df-3an
    @1
    @45
    @43
    @5
    @6
    @7
    cV
    cW
    eqwrds3
    ex
    syl5bir
    expd
    adantr
    imp31
    rexbidva
    2rexbidva
    mpbird
    @10
    @4
    va
    vb
    cV
    cV
    @41
    @9
    @4
    vc
    cV
    @44
    @9
    @4
    @44
    @9
    wa
    #
    @4
    @8
    @0
    wcel
    #
    @8
    chash
    cfv
    #
    c3
    wceq
    #
    wa
    #
    @46
    @47
    @49
    @39
    @40
    @42
    @47
    @9
    @5
    @6
    @7
    cV
    s3cl
    ad4ant123
    @5
    @6
    @7
    s3len
    jctir
    @9
    @4
    @50
    wb
    @44
    @9
    @1
    @47
    @3
    @49
    cW
    @8
    @0
    eleq1
    @9
    @2
    @48
    c3
    cW
    @8
    chash
    fveq2
    eqeq1d
    anbi12d
    adantl
    mpbird
    ex
    rexlimdva
    rexlimivv
    impbii
end
