include "cufil.mm"
include "cfv.mm"
include "wcel.mm"
include "cfil.mm"
include "cv.mm"
include "wss.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "ufilfil.mm"
include "ufilmax.mm"
include "3expia.mm"
include "ralrimiva.mm"
include "jca.mm"
include "cdif.mm"
include "wo.mm"
include "cpw.mm"
include "simpl.mm"
include "selpw.mm"
include "wn.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "csn.mm"
include "cun.mm"
include "cfi.mm"
include "cfg.mm"
include "co.mm"
include "cvv.mm"
include "simpll.mm"
include "snex.mm"
include "unexg.mm"
include "sylancl.mm"
include "ssfii.mm"
include "syl.mm"
include "cfbas.mm"
include "filsspw.mm"
include "ad2antrr.mm"
include "biimpri.mm"
include "ad2antlr.mm"
include "snssd.mm"
include "unssd.mm"
include "ssun2.mm"
include "vex.mm"
include "snnz.mm"
include "ssn0.mm"
include "mp2an.mm"
include "a1i.mm"
include "simpr.mm"
include "ineq2.mm"
include "neeq1d.mm"
include "ralsn.mm"
include "ralbii.mm"
include "sylibr.mm"
include "wb.mm"
include "filfbas.mm"
include "simplr.mm"
include "inss2.mm"
include "filtop.mm"
include "adantr.mm"
include "ineq1.mm"
include "rspcva.mm"
include "sylan.mm"
include "sylancr.mm"
include "snfbas.mm"
include "syl3anc.mm"
include "fbunfip.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "w3a.mm"
include "fsubbas.mm"
include "mpbir3and.mm"
include "ssfg.mm"
include "sstrd.mm"
include "unssad.mm"
include "fgcl.mm"
include "sseq2.mm"
include "eqeq2.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "3syl.mm"
include "mpid.mm"
include "vsnid.mm"
include "sselii.mm"
include "sseldd.mm"
include "eleq2.mm"
include "syl5ibrcom.mm"
include "syld.mm"
include "impancom.mm"
include "an32s.mm"
include "con3d.mm"
include "wrex.mm"
include "rexnal.mm"
include "nne.mm"
include "filelss.mm"
include "reldisj.mm"
include "difss.mm"
include "filss.mm"
include "3exp2.mm"
include "mpii.mm"
include "imp.mm"
include "sylbid.mm"
include "syl5bi.mm"
include "rexlimdva.mm"
include "syl5bir.mm"
include "orrd.mm"
include "sylan2b.mm"
include "isufil.mm"
include "sylanbrc.mm"
include "impbii.mm"

theorem isufil2
  let vf: setvar f
  let cF: class F
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cG: class G

  disjoint F f
  disjoint X f
  disjoint f x
  disjoint f y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint S x
  disjoint X x
  disjoint X y
  disjoint G x
  assert |- ( F e. ( UFil ` X ) <-> ( F e. ( Fil ` X ) /\ A. f e. ( Fil ` X ) ( F C_ f -> F = f ) ) )

  proof
    cF
    cX
    cufil
    cfv
    wcel
    #
    cF
    cX
    cfil
    cfv
    #
    wcel
    #
    cF
    vf
    cv
    #
    wss
    #
    cF
    @3
    wceq
    #
    wi
    #
    vf
    @1
    wral
    #
    wa
    #
    @0
    @2
    @7
    cF
    cX
    ufilfil
    @0
    @6
    vf
    @1
    @0
    @3
    @1
    wcel
    @4
    @5
    cF
    @3
    cX
    ufilmax
    3expia
    ralrimiva
    jca
    @8
    @2
    vx
    cv
    #
    cF
    wcel
    #
    cX
    @9
    cdif
    #
    cF
    wcel
    #
    wo
    #
    vx
    cX
    cpw
    #
    wral
    @0
    @2
    @7
    simpl
    @8
    @13
    vx
    @14
    @9
    @14
    wcel
    #
    @8
    @9
    cX
    wss
    #
    @13
    vx
    cX
    selpw
    #
    @8
    @16
    wa
    #
    @10
    @12
    @18
    @10
    wn
    vy
    cv
    #
    @9
    cin
    #
    c0
    wne
    #
    vy
    cF
    wral
    #
    wn
    #
    @12
    @18
    @22
    @10
    @2
    @16
    @7
    @22
    @10
    wi
    @2
    @16
    wa
    #
    @22
    @7
    @10
    @24
    @22
    wa
    #
    @7
    cF
    cX
    cF
    @9
    csn
    #
    cun
    #
    cfi
    cfv
    #
    cfg
    co
    #
    wceq
    #
    @10
    @25
    @7
    cF
    @29
    wss
    #
    @30
    @25
    cF
    @26
    @29
    @25
    @27
    @28
    @29
    @25
    @27
    cvv
    wcel
    #
    @27
    @28
    wss
    @25
    @2
    @26
    cvv
    wcel
    @32
    @2
    @16
    @22
    simpll
    @9
    snex
    cF
    @26
    @1
    cvv
    unexg
    sylancl
    @27
    cvv
    ssfii
    syl
    @25
    @28
    cX
    cfbas
    cfv
    #
    wcel
    #
    @28
    @29
    wss
    @25
    @34
    @27
    @14
    wss
    #
    @27
    c0
    wne
    #
    c0
    @28
    wcel
    wn
    #
    @25
    cF
    @26
    @14
    @2
    cF
    @14
    wss
    @16
    @22
    cF
    cX
    filsspw
    ad2antrr
    @25
    @9
    @14
    @16
    @15
    @2
    @22
    @15
    @16
    @17
    biimpri
    ad2antlr
    snssd
    unssd
    @36
    @25
    @26
    @27
    wss
    @26
    c0
    wne
    @36
    @26
    cF
    ssun2
    #
    @9
    vx
    vex
    #
    snnz
    @26
    @27
    ssn0
    mp2an
    a1i
    @25
    @37
    @19
    @3
    cin
    #
    c0
    wne
    #
    vf
    @26
    wral
    #
    vy
    cF
    wral
    #
    @25
    @22
    @43
    @24
    @22
    simpr
    @42
    @21
    vy
    cF
    @41
    @21
    vf
    @9
    @39
    @3
    @9
    wceq
    @40
    @20
    c0
    @3
    @9
    @19
    ineq2
    neeq1d
    ralsn
    ralbii
    sylibr
    @25
    cF
    @33
    wcel
    #
    @26
    @33
    wcel
    #
    @37
    @43
    wb
    @2
    @44
    @16
    @22
    cF
    cX
    filfbas
    ad2antrr
    @25
    @16
    @9
    c0
    wne
    #
    cX
    cF
    wcel
    #
    @45
    @2
    @16
    @22
    simplr
    @25
    cX
    @9
    cin
    #
    @9
    wss
    @48
    c0
    wne
    #
    @46
    cX
    @9
    inss2
    @24
    @47
    @22
    @49
    @2
    @47
    @16
    cF
    cX
    filtop
    #
    adantr
    @21
    @49
    vy
    cX
    cF
    @19
    cX
    wceq
    @20
    @48
    c0
    @19
    cX
    @9
    ineq1
    neeq1d
    rspcva
    sylan
    @48
    @9
    ssn0
    sylancr
    @2
    @47
    @16
    @22
    @50
    ad2antrr
    #
    @9
    cX
    cF
    snfbas
    syl3anc
    vy
    vf
    cF
    @26
    cX
    cX
    fbunfip
    syl2anc
    mpbird
    @25
    @47
    @34
    @35
    @36
    @37
    w3a
    wb
    @51
    @27
    cF
    cX
    fsubbas
    syl
    mpbir3and
    #
    @28
    cX
    ssfg
    syl
    sstrd
    #
    unssad
    @25
    @34
    @29
    @1
    wcel
    @7
    @31
    @30
    wi
    #
    wi
    @52
    @28
    cX
    fgcl
    @6
    @54
    vf
    @29
    @1
    @3
    @29
    wceq
    @4
    @31
    @5
    @30
    @3
    @29
    cF
    sseq2
    @3
    @29
    cF
    eqeq2
    imbi12d
    rspcv
    3syl
    mpid
    @25
    @10
    @30
    @9
    @29
    wcel
    @25
    @27
    @29
    @9
    @53
    @9
    @27
    wcel
    @25
    @26
    @27
    @9
    @38
    vx
    vsnid
    sselii
    a1i
    sseldd
    cF
    @29
    @9
    eleq2
    syl5ibrcom
    syld
    impancom
    an32s
    con3d
    @2
    @23
    @12
    wi
    @7
    @16
    @23
    @21
    wn
    #
    vy
    cF
    wrex
    @2
    @12
    @21
    vy
    cF
    rexnal
    @2
    @55
    @12
    vy
    cF
    @55
    @20
    c0
    wceq
    #
    @2
    @19
    cF
    wcel
    #
    wa
    #
    @12
    @20
    c0
    nne
    @58
    @56
    @19
    @11
    wss
    #
    @12
    @58
    @19
    cX
    wss
    @56
    @59
    wb
    @19
    cF
    cX
    filelss
    @19
    @9
    cX
    reldisj
    syl
    @2
    @57
    @59
    @12
    wi
    #
    @2
    @57
    @11
    cX
    wss
    #
    @60
    cX
    @9
    difss
    @2
    @57
    @61
    @59
    @12
    @19
    @11
    cF
    cX
    filss
    3exp2
    mpii
    imp
    sylbid
    syl5bi
    rexlimdva
    syl5bir
    ad2antrr
    syld
    orrd
    sylan2b
    ralrimiva
    vx
    cF
    cX
    isufil
    sylanbrc
    impbii
end
