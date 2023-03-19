include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "c0p.mm"
include "wne.mm"
include "wa.mm"
include "cdgr.mm"
include "wceq.mm"
include "cfn.mm"
include "chash.mm"
include "cle.mm"
include "wbr.mm"
include "eqid.mm"
include "cv.mm"
include "ccnv.mm"
include "cc0.mm"
include "csn.mm"
include "cima.mm"
include "wi.mm"
include "cc.mm"
include "cdif.mm"
include "wral.mm"
include "cn0.mm"
include "dgrcl.mm"
include "adantr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "eqeq2.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "c0.mm"
include "wn.mm"
include "eldifsni.mm"
include "cxp.mm"
include "simplr.mm"
include "wb.mm"
include "eldifi.mm"
include "ad2antrr.mm"
include "0dgrb.mm"
include "syl.mm"
include "mpbid.mm"
include "fveq1d.mm"
include "wf.mm"
include "wfn.mm"
include "plyf.mm"
include "ffn.mm"
include "fniniseg.mm"
include "4syl.mm"
include "biimpa.mm"
include "simprd.mm"
include "simpld.mm"
include "fvex.mm"
include "fvconst2.mm"
include "3eqtr3rd.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "eqtrd.mm"
include "df-0p.mm"
include "syl6eqr.mm"
include "ex.mm"
include "necon3ad.mm"
include "mpd.mm"
include "eq0rdv.mm"
include "nn0ge0.mm"
include "3syl.mm"
include "id.mm"
include "0fin.mm"
include "syl6eqel.mm"
include "biantrurd.mm"
include "fveq2.mm"
include "hash0.mm"
include "syl6eq.mm"
include "breq1d.mm"
include "bitr3d.mm"
include "syl5ibrcom.mm"
include "syld.mm"
include "rgen.mm"
include "eqeq1d.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "eleq1d.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "ad2antlr.mm"
include "a1dd.mm"
include "wex.mm"
include "n0.mm"
include "simplll.mm"
include "simpllr.mm"
include "simprl.mm"
include "simprr.mm"
include "fta1lem.mm"
include "exp32.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "pm2.61dne.mm"
include "com23.mm"
include "ralrimdva.mm"
include "nn0ind.mm"
include "plyssc.mm"
include "sseli.mm"
include "eldifsn.mm"
include "rspcv.mm"
include "sylbir.mm"
include "sylan.mm"
include "mpi.mm"

theorem fta1
  let cR: class R
  let cS: class S
  let cF: class F
  let vg: setvar g
  let vx: setvar x
  let cA: class A
  let cD: class D
  let vd: setvar d
  let vf: setvar f
  let wph: wff ph
  assume fta1.1: |- R = ( `' F " { 0 } )


  assert |- ( ( F e. ( Poly ` S ) /\ F =/= 0p ) -> ( R e. Fin /\ ( # ` R ) <_ ( deg ` F ) ) )

  proof
    cF
    cS
    cply
    cfv
    #
    wcel
    #
    cF
    c0p
    wne
    #
    wa
    #
    cF
    cdgr
    cfv
    #
    @4
    wceq
    #
    cR
    cfn
    wcel
    #
    cR
    chash
    cfv
    #
    @4
    cle
    wbr
    #
    wa
    #
    @4
    eqid
    @3
    vf
    cv
    #
    cdgr
    cfv
    #
    @4
    wceq
    #
    @10
    ccnv
    #
    cc0
    csn
    #
    cima
    #
    cfn
    wcel
    #
    @15
    chash
    cfv
    #
    @11
    cle
    wbr
    #
    wa
    #
    wi
    #
    vf
    cc
    cply
    cfv
    #
    c0p
    csn
    #
    cdif
    #
    wral
    #
    @5
    @9
    wi
    #
    @3
    @4
    cn0
    wcel
    #
    @24
    @1
    @26
    @2
    cS
    cF
    dgrcl
    adantr
    @11
    vx
    cv
    #
    wceq
    #
    @19
    wi
    #
    vf
    @23
    wral
    @11
    cc0
    wceq
    #
    @19
    wi
    #
    vf
    @23
    wral
    @11
    vd
    cv
    #
    wceq
    #
    @19
    wi
    #
    vf
    @23
    wral
    #
    @11
    @32
    c1
    caddc
    co
    #
    wceq
    #
    @19
    wi
    #
    vf
    @23
    wral
    #
    @24
    vx
    vd
    @4
    @27
    cc0
    wceq
    #
    @29
    @31
    vf
    @23
    @40
    @28
    @30
    @19
    @27
    cc0
    @11
    eqeq2
    imbi1d
    ralbidv
    @27
    @32
    wceq
    #
    @29
    @34
    vf
    @23
    @41
    @28
    @33
    @19
    @27
    @32
    @11
    eqeq2
    imbi1d
    ralbidv
    @27
    @36
    wceq
    #
    @29
    @38
    vf
    @23
    @42
    @28
    @37
    @19
    @27
    @36
    @11
    eqeq2
    imbi1d
    ralbidv
    @27
    @4
    wceq
    #
    @29
    @20
    vf
    @23
    @43
    @28
    @12
    @19
    @27
    @4
    @11
    eqeq2
    imbi1d
    ralbidv
    @31
    vf
    @23
    @10
    @23
    wcel
    #
    @30
    @15
    c0
    wceq
    #
    @19
    @44
    @30
    @45
    @44
    @30
    wa
    #
    vx
    @15
    @46
    @10
    c0p
    wne
    #
    @27
    @15
    wcel
    #
    wn
    @44
    @47
    @30
    @10
    @21
    c0p
    eldifsni
    adantr
    @46
    @48
    @10
    c0p
    @46
    @48
    @10
    c0p
    wceq
    @46
    @48
    wa
    #
    @10
    cc
    @14
    cxp
    #
    c0p
    @49
    @10
    cc
    cc0
    @10
    cfv
    #
    csn
    #
    cxp
    #
    @50
    @49
    @30
    @10
    @53
    wceq
    #
    @44
    @30
    @48
    simplr
    @49
    @10
    @21
    wcel
    #
    @30
    @54
    wb
    @44
    @55
    @30
    @48
    @10
    @21
    @22
    eldifi
    #
    ad2antrr
    cc
    @10
    0dgrb
    syl
    mpbid
    #
    @49
    @52
    @14
    cc
    @49
    @51
    cc0
    @49
    @27
    @10
    cfv
    #
    @27
    @53
    cfv
    #
    cc0
    @51
    @49
    @27
    @10
    @53
    @57
    fveq1d
    @49
    @27
    cc
    wcel
    #
    @58
    cc0
    wceq
    #
    @46
    @48
    @60
    @61
    wa
    #
    @46
    @55
    cc
    cc
    @10
    wf
    @10
    cc
    wfn
    @48
    @62
    wb
    @44
    @55
    @30
    @56
    adantr
    cc
    @10
    plyf
    cc
    cc
    @10
    ffn
    cc
    cc0
    @27
    @10
    fniniseg
    4syl
    biimpa
    #
    simprd
    @49
    @60
    @59
    @51
    wceq
    @49
    @60
    @61
    @63
    simpld
    cc
    @51
    @27
    cc0
    @10
    fvex
    fvconst2
    syl
    3eqtr3rd
    sneqd
    xpeq2d
    eqtrd
    df-0p
    syl6eqr
    ex
    necon3ad
    mpd
    eq0rdv
    ex
    @44
    @19
    @45
    cc0
    @11
    cle
    wbr
    #
    @44
    @55
    @11
    cn0
    wcel
    @64
    @56
    cc
    @10
    dgrcl
    @11
    nn0ge0
    3syl
    #
    @45
    @18
    @19
    @64
    @45
    @16
    @18
    @45
    @15
    c0
    cfn
    @45
    id
    0fin
    syl6eqel
    biantrurd
    @45
    @17
    cc0
    @11
    cle
    @45
    @17
    c0
    chash
    cfv
    cc0
    @15
    c0
    chash
    fveq2
    hash0
    syl6eq
    breq1d
    bitr3d
    #
    syl5ibrcom
    syld
    rgen
    @35
    vg
    cv
    #
    cdgr
    cfv
    #
    @32
    wceq
    #
    @67
    ccnv
    #
    @14
    cima
    #
    cfn
    wcel
    #
    @71
    chash
    cfv
    #
    @68
    cle
    wbr
    #
    wa
    #
    wi
    #
    vg
    @23
    wral
    #
    @32
    cn0
    wcel
    #
    @39
    @34
    @76
    vf
    vg
    @23
    @10
    @67
    wceq
    #
    @33
    @69
    @19
    @75
    @79
    @11
    @68
    @32
    @10
    @67
    cdgr
    fveq2
    #
    eqeq1d
    @79
    @16
    @72
    @18
    @74
    @79
    @15
    @71
    cfn
    @79
    @13
    @70
    @14
    @10
    @67
    cnveq
    imaeq1d
    #
    eleq1d
    @79
    @17
    @73
    @11
    @68
    cle
    @79
    @15
    @71
    chash
    @81
    fveq2d
    @80
    breq12d
    anbi12d
    imbi12d
    cbvralv
    @78
    @77
    @38
    vf
    @23
    @78
    @44
    wa
    #
    @37
    @77
    @19
    @82
    @37
    @77
    @19
    wi
    #
    @82
    @37
    wa
    #
    @83
    @15
    c0
    @84
    @45
    @19
    @77
    @84
    @19
    @45
    @64
    @44
    @64
    @78
    @37
    @65
    ad2antlr
    @66
    syl5ibrcom
    a1dd
    @15
    c0
    wne
    @48
    vx
    wex
    @84
    @83
    vx
    @15
    n0
    @84
    @48
    @83
    vx
    @84
    @48
    @77
    @19
    @84
    @48
    @77
    wa
    #
    wa
    @27
    @32
    @15
    vg
    @10
    @15
    eqid
    @78
    @44
    @37
    @85
    simplll
    @78
    @44
    @37
    @85
    simpllr
    @82
    @37
    @85
    simplr
    @84
    @48
    @77
    simprl
    @84
    @48
    @77
    simprr
    fta1lem
    exp32
    exlimdv
    syl5bi
    pm2.61dne
    ex
    com23
    ralrimdva
    syl5bi
    nn0ind
    syl
    @1
    cF
    @21
    wcel
    #
    @2
    @24
    @25
    wi
    #
    @0
    @21
    cF
    cS
    plyssc
    sseli
    @86
    @2
    wa
    cF
    @23
    wcel
    @87
    cF
    @21
    c0p
    eldifsn
    @20
    @25
    vf
    cF
    @23
    @10
    cF
    wceq
    #
    @12
    @5
    @19
    @9
    @88
    @11
    @4
    @4
    @10
    cF
    cdgr
    fveq2
    #
    eqeq1d
    @88
    @16
    @6
    @18
    @8
    @88
    @15
    cR
    cfn
    @88
    @15
    cF
    ccnv
    #
    @14
    cima
    cR
    @88
    @13
    @90
    @14
    @10
    cF
    cnveq
    imaeq1d
    fta1.1
    syl6eqr
    #
    eleq1d
    @88
    @17
    @7
    @11
    @4
    cle
    @88
    @15
    cR
    chash
    @91
    fveq2d
    @89
    breq12d
    anbi12d
    imbi12d
    rspcv
    sylbir
    sylan
    mpd
    mpi
end
