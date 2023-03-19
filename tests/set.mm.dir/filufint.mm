include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "cufil.mm"
include "crab.mm"
include "cint.mm"
include "wi.mm"
include "wral.mm"
include "vex.mm"
include "elintrab.mm"
include "wn.mm"
include "wa.mm"
include "wrex.mm"
include "w3a.mm"
include "cdif.mm"
include "csn.mm"
include "cun.mm"
include "cfi.mm"
include "cfg.mm"
include "co.mm"
include "cfbas.mm"
include "cpw.mm"
include "c0.mm"
include "wne.mm"
include "filsspw.mm"
include "3ad2ant1.mm"
include "difss.mm"
include "cvv.mm"
include "wb.mm"
include "filtop.mm"
include "difexg.mm"
include "syl.mm"
include "elpwg.mm"
include "mpbiri.mm"
include "snssd.mm"
include "unssd.mm"
include "ssun1.mm"
include "filn0.mm"
include "ssn0.mm"
include "sylancr.mm"
include "cin.mm"
include "wceq.mm"
include "elsni.mm"
include "filelss.mm"
include "3adant3.mm"
include "reldisj.mm"
include "dfss4.mm"
include "biimpi.mm"
include "sseq2d.mm"
include "3ad2ant3.mm"
include "bitrd.mm"
include "filss.mm"
include "3exp2.mm"
include "3imp.mm"
include "sylbid.mm"
include "necon3bd.mm"
include "3exp.mm"
include "com24.mm"
include "3imp1.mm"
include "ineq2.mm"
include "neeq1d.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "sylan2i.mm"
include "ralrimivv.mm"
include "filfbas.mm"
include "a1i.mm"
include "3ad2ant2.mm"
include "difeq2.mm"
include "dif0.mm"
include "syl6eq.mm"
include "eqtr3d.mm"
include "eqeltrd.mm"
include "3expia.mm"
include "ex.mm"
include "com23.mm"
include "snfbas.mm"
include "syl3anc.mm"
include "fbunfip.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "fsubbas.mm"
include "mpbir3and.mm"
include "fgcl.mm"
include "filssufil.mm"
include "snex.mm"
include "unexg.mm"
include "mpan2.mm"
include "ssfii.mm"
include "unssad.mm"
include "ssfg.mm"
include "sstrd.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "ufilfil.mm"
include "0nelfil.mm"
include "ad2antlr.mm"
include "disjdif.mm"
include "simprr.mm"
include "unssbd.mm"
include "adantr.mm"
include "simprl.mm"
include "snidg.mm"
include "sseldd.mm"
include "filin.mm"
include "syl5eqelr.mm"
include "expr.mm"
include "mtod.mm"
include "jca.mm"
include "exp31.mm"
include "reximdvai.mm"
include "syl5.mm"
include "mpd.mm"
include "con3d.mm"
include "impcom.mm"
include "a1d.mm"
include "ancld.mm"
include "reximdva.mm"
include "syl5com.mm"
include "pm2.61d.mm"
include "rexanali.mm"
include "syl6ib.mm"
include "con4d.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "ssintub.mm"
include "eqssd.mm"

theorem filufint
  let vf: setvar f
  let cF: class F
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint F f
  disjoint X f
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( F e. ( Fil ` X ) -> |^| { f e. ( UFil ` X ) | F C_ f } = F )

  proof
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
    vf
    cX
    cufil
    cfv
    #
    crab
    cint
    #
    cF
    @1
    vx
    @5
    cF
    vx
    cv
    #
    @5
    wcel
    @3
    @6
    @2
    wcel
    #
    wi
    vf
    @4
    wral
    #
    @1
    @6
    cF
    wcel
    #
    @3
    vf
    @6
    @4
    vx
    vex
    elintrab
    @1
    @9
    @8
    @1
    @9
    wn
    #
    @3
    @7
    wn
    #
    wa
    #
    vf
    @4
    wrex
    #
    @8
    wn
    @1
    @10
    @13
    @1
    @10
    wa
    @6
    cX
    wss
    #
    @13
    @1
    @10
    @14
    @13
    @1
    @10
    @14
    w3a
    #
    cX
    cF
    cX
    @6
    cdif
    #
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
    @0
    wcel
    #
    @13
    @15
    @19
    cX
    cfbas
    cfv
    #
    wcel
    #
    @21
    @15
    @23
    @18
    cX
    cpw
    #
    wss
    #
    @18
    c0
    wne
    #
    c0
    @19
    wcel
    wn
    #
    @15
    cF
    @17
    @24
    @1
    @10
    cF
    @24
    wss
    @14
    cF
    cX
    filsspw
    3ad2ant1
    @15
    @16
    @24
    @15
    @16
    @24
    wcel
    #
    @16
    cX
    wss
    #
    cX
    @6
    difss
    #
    @15
    @16
    cvv
    wcel
    #
    @28
    @29
    wb
    @1
    @10
    @31
    @14
    @1
    cX
    cF
    wcel
    #
    @31
    cF
    cX
    filtop
    #
    cX
    @6
    cF
    difexg
    syl
    #
    3ad2ant1
    @16
    cX
    cvv
    elpwg
    syl
    mpbiri
    snssd
    unssd
    @1
    @10
    @26
    @14
    @1
    cF
    @18
    wss
    cF
    c0
    wne
    @26
    cF
    @17
    ssun1
    cF
    cX
    filn0
    cF
    @18
    ssn0
    sylancr
    3ad2ant1
    @15
    @27
    vy
    cv
    #
    vz
    cv
    #
    cin
    #
    c0
    wne
    #
    vz
    @17
    wral
    vy
    cF
    wral
    #
    @15
    @38
    vy
    vz
    cF
    @17
    @36
    @17
    wcel
    @15
    @35
    cF
    wcel
    #
    @36
    @16
    wceq
    #
    @38
    @36
    @16
    elsni
    @15
    @40
    @41
    @38
    @15
    @40
    wa
    @38
    @41
    @35
    @16
    cin
    #
    c0
    wne
    #
    @1
    @10
    @14
    @40
    @43
    @1
    @40
    @14
    @10
    @43
    @1
    @40
    @14
    @10
    @43
    wi
    @1
    @40
    @14
    w3a
    #
    @9
    @42
    c0
    @44
    @42
    c0
    wceq
    #
    @35
    @6
    wss
    #
    @9
    @44
    @45
    @35
    cX
    @16
    cdif
    #
    wss
    #
    @46
    @44
    @35
    cX
    wss
    #
    @45
    @48
    wb
    @1
    @40
    @49
    @14
    @35
    cF
    cX
    filelss
    3adant3
    @35
    @16
    cX
    reldisj
    syl
    @14
    @1
    @48
    @46
    wb
    @40
    @14
    @47
    @6
    @35
    @14
    @47
    @6
    wceq
    #
    @6
    cX
    dfss4
    biimpi
    #
    sseq2d
    3ad2ant3
    bitrd
    @1
    @40
    @14
    @46
    @9
    wi
    @1
    @40
    @14
    @46
    @9
    @35
    @6
    cF
    cX
    filss
    3exp2
    3imp
    sylbid
    necon3bd
    3exp
    com24
    3imp1
    @41
    @37
    @42
    c0
    @36
    @16
    @35
    ineq2
    neeq1d
    syl5ibrcom
    expimpd
    sylan2i
    ralrimivv
    @15
    cF
    @22
    wcel
    #
    @17
    @22
    wcel
    #
    @27
    @39
    wb
    @1
    @10
    @52
    @14
    cF
    cX
    filfbas
    3ad2ant1
    @15
    @29
    @16
    c0
    wne
    #
    @32
    @53
    @29
    @15
    @30
    a1i
    @1
    @10
    @14
    @54
    @1
    @14
    @10
    @54
    @1
    @14
    @10
    @54
    wi
    @1
    @14
    wa
    @9
    @16
    c0
    @1
    @14
    @16
    c0
    wceq
    #
    @9
    @1
    @14
    @55
    w3a
    #
    @6
    cX
    cF
    @56
    @47
    @6
    cX
    @14
    @1
    @50
    @55
    @51
    3ad2ant2
    @55
    @1
    @47
    cX
    wceq
    @14
    @55
    @47
    cX
    c0
    cdif
    cX
    @16
    c0
    cX
    difeq2
    cX
    dif0
    syl6eq
    3ad2ant3
    eqtr3d
    @1
    @14
    @32
    @55
    @33
    3ad2ant1
    eqeltrd
    3expia
    necon3bd
    ex
    com23
    3imp
    @1
    @10
    @32
    @14
    @33
    3ad2ant1
    @16
    cX
    cF
    snfbas
    syl3anc
    vy
    vz
    cF
    @17
    cX
    cX
    fbunfip
    syl2anc
    mpbird
    @1
    @10
    @23
    @25
    @26
    @27
    w3a
    wb
    #
    @14
    @1
    @32
    @57
    @33
    @18
    cF
    cX
    fsubbas
    syl
    3ad2ant1
    mpbir3and
    #
    @19
    cX
    fgcl
    syl
    @21
    @20
    @2
    wss
    #
    vf
    @4
    wrex
    @15
    @13
    vf
    @20
    cX
    filssufil
    @15
    @59
    @12
    vf
    @4
    @15
    @2
    @4
    wcel
    #
    @59
    @12
    @15
    @60
    wa
    #
    @59
    wa
    #
    @3
    @11
    @62
    cF
    @20
    @2
    @15
    cF
    @20
    wss
    @60
    @59
    @15
    cF
    @19
    @20
    @15
    cF
    @17
    @19
    @1
    @10
    @18
    @19
    wss
    #
    @14
    @1
    @18
    cvv
    wcel
    #
    @63
    @1
    @17
    cvv
    wcel
    @64
    @16
    snex
    cF
    @17
    @0
    cvv
    unexg
    mpan2
    @18
    cvv
    ssfii
    syl
    #
    3ad2ant1
    unssad
    @15
    @23
    @19
    @20
    wss
    #
    @58
    @19
    cX
    ssfg
    #
    syl
    sstrd
    ad2antrr
    @61
    @59
    simpr
    sstrd
    @62
    @7
    c0
    @2
    wcel
    #
    @60
    @68
    wn
    #
    @15
    @59
    @60
    @2
    @0
    wcel
    #
    @69
    @2
    cX
    ufilfil
    #
    @2
    cX
    0nelfil
    syl
    ad2antlr
    @61
    @59
    @7
    @68
    @61
    @59
    @7
    wa
    #
    wa
    #
    c0
    @6
    @16
    cin
    #
    @2
    @6
    cX
    disjdif
    @73
    @70
    @7
    @16
    @2
    wcel
    @74
    @2
    wcel
    @60
    @70
    @15
    @72
    @71
    ad2antlr
    @61
    @59
    @7
    simprr
    @73
    @17
    @2
    @16
    @73
    @17
    @20
    @2
    @61
    @17
    @20
    wss
    @72
    @61
    @17
    @19
    @20
    @15
    @17
    @19
    wss
    #
    @60
    @1
    @10
    @75
    @14
    @1
    cF
    @17
    @19
    @65
    unssbd
    3ad2ant1
    adantr
    @61
    @23
    @66
    @15
    @23
    @60
    @58
    adantr
    @67
    syl
    sstrd
    adantr
    @61
    @59
    @7
    simprl
    sstrd
    @15
    @16
    @17
    wcel
    #
    @60
    @72
    @1
    @10
    @76
    @14
    @1
    @31
    @76
    @34
    @16
    cvv
    snidg
    syl
    3ad2ant1
    ad2antrr
    sseldd
    @6
    @16
    @2
    cX
    filin
    syl3anc
    syl5eqelr
    expr
    mtod
    jca
    exp31
    reximdvai
    syl5
    mpd
    3expia
    @1
    @14
    wn
    #
    @13
    wi
    @10
    @1
    @3
    vf
    @4
    wrex
    @77
    @13
    vf
    cF
    cX
    filssufil
    @77
    @3
    @12
    vf
    @4
    @77
    @60
    wa
    #
    @3
    @11
    @78
    @11
    @3
    @60
    @77
    @11
    @60
    @7
    @14
    @60
    @70
    @7
    @14
    wi
    @71
    @70
    @7
    @14
    @6
    @2
    cX
    filelss
    ex
    syl
    con3d
    impcom
    a1d
    ancld
    reximdva
    syl5com
    adantr
    pm2.61d
    ex
    @3
    @7
    vf
    @4
    rexanali
    syl6ib
    con4d
    syl5bi
    ssrdv
    cF
    @5
    wss
    @1
    vf
    cF
    @4
    ssintub
    a1i
    eqssd
end
