include "crg.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cima.mm"
include "cfv.mm"
include "clmod.mm"
include "clss.mm"
include "frlmlmod.mm"
include "3adant3.mm"
include "eqid.mm"
include "frlmsslss2.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "csupp.mm"
include "co.mm"
include "wf.mm"
include "uvcff.mm"
include "adantr.mm"
include "simp3.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "cbs.mm"
include "simpl2.mm"
include "frlmbasf.mm"
include "syl2anc.mm"
include "cdif.mm"
include "simpll1.mm"
include "simpll2.mm"
include "eldifi.mm"
include "adantl.mm"
include "wne.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "disjdif.mm"
include "disjne.mm"
include "mp3an1.mm"
include "adantll.mm"
include "uvcvv0.mm"
include "suppss.mm"
include "oveq1.mm"
include "sseq1d.mm"
include "elrab2.mm"
include "sylanbrc.mm"
include "ralrimiva.mm"
include "wfun.mm"
include "cdm.mm"
include "wb.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "fnfun.mm"
include "fndm.mm"
include "sseqtr4d.mm"
include "funimass4.mm"
include "mpbird.mm"
include "lspssp.mm"
include "syl3anc.mm"
include "cvsca.mm"
include "cof.mm"
include "cgsu.mm"
include "simpl1.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "a1i.mm"
include "uvcresum.mm"
include "c0g.mm"
include "cabl.mm"
include "lmodabl.mm"
include "csubg.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "syl5ss.mm"
include "lspcl.mm"
include "lsssubg.mm"
include "3ad2antl2.mm"
include "inidm.mm"
include "offn.mm"
include "syldan.mm"
include "adantrr.mm"
include "simprr.mm"
include "fnfvof.mm"
include "syl22anc.mm"
include "csca.mm"
include "sseli.mm"
include "sylan2.mm"
include "adantrl.mm"
include "frlmsca.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "lspssid.mm"
include "wi.mm"
include "funfvima2.mm"
include "imp.mm"
include "sseldd.mm"
include "lssvscl.mm"
include "anassrs.mm"
include "adantlrr.mm"
include "wn.mm"
include "id.mm"
include "simplrr.mm"
include "simpr.mm"
include "eldifd.mm"
include "cvv.mm"
include "simprbi.mm"
include "fvex.mm"
include "eqeltri.mm"
include "suppssr.mm"
include "syl5eq.mm"
include "ad2antrr.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "ffvelrnda.mm"
include "lmod0vs.mm"
include "lss0cl.mm"
include "eqeltrd.mm"
include "pm2.61dan.mm"
include "expr.mm"
include "ralrimiv.mm"
include "ffnfv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cfn.mm"
include "frlmbasfsupp.mm"
include "fsuppimpd.mm"
include "dffn2.mm"
include "sylib.mm"
include "ssid.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "3eqtrd.mm"
include "ssfi.mm"
include "cmap.mm"
include "simp2.mm"
include "frlmbasmap.mm"
include "elmapfn.mm"
include "ovexd.mm"
include "funisfsupp.mm"
include "gsumsubgcl.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem frlmsslsp
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cR: class R
  let cU: class U
  let cI: class I
  let cJ: class J
  let cK: class K
  let cV: class V
  let cY: class Y
  let c.0: class .0.
  let vy: setvar y
  let vz: setvar z
  assume frlmsslsp.y: |- Y = ( R freeLMod I )
  assume frlmsslsp.u: |- U = ( R unitVec I )
  assume frlmsslsp.k: |- K = ( LSpan ` Y )
  assume frlmsslsp.b: |- B = ( Base ` Y )
  assume frlmsslsp.z: |- .0. = ( 0g ` R )
  assume frlmsslsp.c: |- C = { x e. B | ( x supp .0. ) C_ J }

  disjoint Y x
  disjoint U x
  disjoint B x
  disjoint .0. x
  disjoint R x
  disjoint I x
  disjoint V x
  disjoint J x
  disjoint K x
  disjoint Y y
  disjoint Y z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint U y
  disjoint U z
  disjoint B y
  disjoint .0. y
  disjoint R y
  disjoint R z
  disjoint C y
  disjoint C z
  disjoint I y
  disjoint I z
  disjoint V y
  disjoint V z
  disjoint J y
  disjoint J z
  disjoint K y
  disjoint K z
  assert |- ( ( R e. Ring /\ I e. V /\ J C_ I ) -> ( K ` ( U " J ) ) = C )

  proof
    cR
    crg
    wcel
    #
    cI
    cV
    wcel
    #
    cJ
    cI
    wss
    #
    w3a
    #
    cU
    cJ
    cima
    #
    cK
    cfv
    #
    cC
    @3
    cY
    clmod
    wcel
    #
    cC
    cY
    clss
    cfv
    #
    wcel
    @4
    cC
    wss
    #
    @5
    cC
    wss
    @0
    @1
    @6
    @2
    cR
    cY
    cI
    cV
    frlmsslsp.y
    frlmlmod
    3adant3
    #
    vx
    cB
    cC
    cR
    @7
    cI
    cJ
    cV
    cY
    c.0
    frlmsslsp.y
    @7
    eqid
    #
    frlmsslsp.b
    frlmsslsp.z
    frlmsslsp.c
    frlmsslss2
    @3
    @8
    vy
    cv
    #
    cU
    cfv
    #
    cC
    wcel
    #
    vy
    cJ
    wral
    #
    @3
    @13
    vy
    cJ
    @3
    @11
    cJ
    wcel
    #
    wa
    #
    @12
    cB
    wcel
    #
    @12
    c.0
    csupp
    co
    #
    cJ
    wss
    #
    @13
    @16
    cI
    cB
    @11
    cU
    @3
    cI
    cB
    cU
    wf
    #
    @15
    @0
    @1
    @20
    @2
    cB
    cR
    cU
    cI
    cV
    cY
    frlmsslsp.u
    frlmsslsp.y
    frlmsslsp.b
    uvcff
    3adant3
    #
    adantr
    @3
    cJ
    cI
    @11
    @0
    @1
    @2
    simp3
    #
    sselda
    #
    ffvelrnd
    #
    @16
    cI
    cR
    cbs
    cfv
    #
    vx
    @12
    cJ
    c.0
    @16
    @1
    @17
    cI
    @25
    @12
    wf
    @0
    @1
    @2
    @15
    simpl2
    @24
    cB
    cR
    cY
    cI
    @25
    cV
    @12
    frlmsslsp.y
    @25
    eqid
    #
    frlmsslsp.b
    frlmbasf
    syl2anc
    @16
    vx
    cv
    #
    cI
    cJ
    cdif
    #
    wcel
    #
    wa
    cR
    cU
    cI
    @11
    @27
    crg
    cV
    c.0
    frlmsslsp.u
    @0
    @1
    @2
    @15
    @29
    simpll1
    @0
    @1
    @2
    @15
    @29
    simpll2
    @16
    @11
    cI
    wcel
    @29
    @23
    adantr
    @29
    @27
    cI
    wcel
    #
    @16
    @27
    cI
    cJ
    eldifi
    adantl
    @15
    @29
    @11
    @27
    wne
    #
    @3
    cJ
    @28
    cin
    c0
    wceq
    @15
    @29
    @31
    cJ
    cI
    disjdif
    cJ
    @28
    @11
    @27
    disjne
    mp3an1
    adantll
    frlmsslsp.z
    uvcvv0
    suppss
    @27
    c.0
    csupp
    co
    #
    cJ
    wss
    #
    @19
    vx
    @12
    cB
    cC
    @27
    @12
    wceq
    @32
    @18
    cJ
    @27
    @12
    c.0
    csupp
    oveq1
    sseq1d
    frlmsslsp.c
    elrab2
    sylanbrc
    ralrimiva
    @3
    cU
    wfun
    #
    cJ
    cU
    cdm
    #
    wss
    #
    @8
    @14
    wb
    @3
    cU
    cI
    wfn
    #
    @34
    @3
    @20
    @37
    @21
    cI
    cB
    cU
    ffn
    #
    syl
    #
    cI
    cU
    fnfun
    syl
    #
    @3
    cJ
    cI
    @35
    @22
    @3
    @37
    @35
    cI
    wceq
    @39
    cI
    cU
    fndm
    syl
    sseqtr4d
    #
    vy
    cJ
    cC
    cU
    funimass4
    syl2anc
    mpbird
    @7
    @4
    cC
    cK
    cY
    @10
    frlmsslsp.k
    lspssp
    syl3anc
    @3
    vy
    cC
    @5
    @3
    @11
    cC
    wcel
    #
    @11
    @5
    wcel
    @3
    @42
    wa
    #
    @11
    cY
    @11
    cU
    cY
    cvsca
    cfv
    #
    cof
    #
    co
    #
    cgsu
    co
    #
    @5
    @43
    @0
    @1
    @11
    cB
    wcel
    #
    @11
    @47
    wceq
    @0
    @1
    @2
    @42
    simpl1
    @0
    @1
    @2
    @42
    simpl2
    #
    @3
    cC
    cB
    @11
    cC
    cB
    wss
    @3
    cC
    @33
    vx
    cB
    crab
    cB
    frlmsslsp.c
    @33
    vx
    cB
    ssrab2
    eqsstri
    #
    a1i
    sselda
    #
    cB
    cR
    @44
    cU
    cI
    cV
    @11
    cY
    frlmsslsp.u
    frlmsslsp.y
    frlmsslsp.b
    @44
    eqid
    #
    uvcresum
    syl3anc
    @43
    cI
    @5
    @46
    cY
    cV
    cY
    c0g
    cfv
    #
    @53
    eqid
    #
    @3
    cY
    cabl
    wcel
    #
    @42
    @3
    @6
    @55
    @9
    cY
    lmodabl
    syl
    adantr
    @49
    @3
    @5
    cY
    csubg
    cfv
    wcel
    #
    @42
    @3
    @6
    @5
    @7
    wcel
    #
    @56
    @9
    @3
    @6
    @4
    cB
    wss
    #
    @57
    @9
    @3
    @4
    cU
    crn
    #
    cB
    cU
    cJ
    imassrn
    @3
    @20
    @59
    cB
    wss
    @21
    cI
    cB
    cU
    frn
    syl
    syl5ss
    #
    @7
    @4
    cK
    cB
    cY
    frlmsslsp.b
    @10
    frlmsslsp.k
    lspcl
    syl2anc
    #
    @7
    @5
    cY
    @10
    lsssubg
    syl2anc
    adantr
    @43
    @46
    cI
    wfn
    #
    vz
    cv
    #
    @46
    cfv
    #
    @5
    wcel
    #
    vz
    cI
    wral
    cI
    @5
    @46
    wf
    @3
    @42
    @48
    @62
    @51
    @3
    @48
    wa
    #
    cI
    cI
    @44
    cI
    @11
    cU
    cV
    cV
    @66
    cI
    @25
    @11
    wf
    #
    @11
    cI
    wfn
    #
    @1
    @0
    @48
    @67
    @2
    cB
    cR
    cY
    cI
    @25
    cV
    @11
    frlmsslsp.y
    @26
    frlmsslsp.b
    frlmbasf
    3ad2antl2
    #
    cI
    @25
    @11
    ffn
    syl
    #
    @3
    @37
    @48
    @39
    adantr
    @0
    @1
    @2
    @48
    simpl2
    #
    @71
    cI
    inidm
    #
    offn
    #
    syldan
    @43
    @65
    vz
    cI
    @3
    @42
    @63
    cI
    wcel
    #
    @65
    @3
    @42
    @74
    wa
    #
    wa
    #
    @64
    @63
    @11
    cfv
    #
    @63
    cU
    cfv
    #
    @44
    co
    #
    @5
    @76
    @68
    @37
    @1
    @74
    @64
    @79
    wceq
    @3
    @42
    @68
    @74
    @3
    @42
    @48
    @68
    @51
    @70
    syldan
    adantrr
    @3
    @37
    @75
    @39
    adantr
    @0
    @1
    @2
    @75
    simpl2
    @3
    @42
    @74
    simprr
    cI
    @44
    @11
    cU
    cV
    @63
    fnfvof
    syl22anc
    @76
    @63
    cJ
    wcel
    #
    @79
    @5
    wcel
    #
    @3
    @42
    @80
    @81
    @74
    @3
    @42
    @80
    @81
    @3
    @42
    @80
    wa
    #
    wa
    #
    @6
    @57
    @77
    cY
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    @78
    @5
    wcel
    @81
    @3
    @6
    @82
    @9
    adantr
    @3
    @57
    @82
    @61
    adantr
    @83
    @77
    @25
    @85
    @83
    cI
    @25
    @63
    @11
    @3
    @42
    @67
    @80
    @42
    @3
    @48
    @67
    cC
    cB
    @11
    @50
    sseli
    #
    @69
    sylan2
    #
    adantrr
    @3
    @80
    @74
    @42
    @3
    cJ
    cI
    @63
    @22
    sselda
    adantrl
    ffvelrnd
    @3
    @25
    @85
    wceq
    @82
    @3
    cR
    @84
    cbs
    @0
    @1
    cR
    @84
    wceq
    @2
    cR
    cY
    cI
    crg
    cV
    frlmsslsp.y
    frlmsca
    3adant3
    #
    fveq2d
    adantr
    eleqtrd
    @83
    @4
    @5
    @78
    @3
    @4
    @5
    wss
    #
    @82
    @3
    @6
    @58
    @89
    @9
    @60
    @4
    cK
    cB
    cY
    frlmsslsp.b
    frlmsslsp.k
    lspssid
    syl2anc
    adantr
    @3
    @80
    @78
    @4
    wcel
    #
    @42
    @3
    @80
    @90
    @3
    @34
    @36
    @80
    @90
    wi
    @40
    @41
    cJ
    @63
    cU
    funfvima2
    syl2anc
    imp
    adantrl
    sseldd
    @85
    @7
    @44
    @5
    @84
    cY
    @77
    @78
    @84
    eqid
    #
    @52
    @85
    eqid
    @10
    lssvscl
    syl22anc
    anassrs
    adantlrr
    @76
    @80
    wn
    #
    wa
    #
    @79
    @53
    @5
    @93
    @79
    @84
    c0g
    cfv
    #
    @78
    @44
    co
    #
    @53
    @93
    @77
    @94
    @78
    @44
    @93
    @77
    c.0
    @94
    @93
    @43
    @63
    @28
    wcel
    @77
    c.0
    wceq
    @76
    @43
    @92
    @3
    @42
    @43
    @74
    @43
    id
    adantrr
    adantr
    @93
    @63
    cI
    cJ
    @3
    @42
    @74
    @92
    simplrr
    @76
    @92
    simpr
    eldifd
    @43
    cI
    @25
    cvv
    @11
    cV
    cJ
    @63
    c.0
    @87
    @42
    @11
    c.0
    csupp
    co
    #
    cJ
    wss
    #
    @3
    @42
    @48
    @97
    @33
    @97
    vx
    @11
    cB
    cC
    @27
    @11
    wceq
    @32
    @96
    cJ
    @27
    @11
    c.0
    csupp
    oveq1
    sseq1d
    frlmsslsp.c
    elrab2
    simprbi
    adantl
    @49
    c.0
    cvv
    wcel
    #
    @43
    c.0
    cR
    c0g
    cfv
    #
    cvv
    frlmsslsp.z
    cR
    c0g
    fvex
    eqeltri
    #
    a1i
    suppssr
    syl2anc
    @3
    c.0
    @94
    wceq
    #
    @75
    @92
    @3
    c.0
    @99
    @94
    frlmsslsp.z
    @3
    cR
    @84
    c0g
    @88
    fveq2d
    syl5eq
    #
    ad2antrr
    eqtrd
    oveq1d
    @93
    @6
    @78
    cB
    wcel
    #
    @95
    @53
    wceq
    @3
    @6
    @75
    @92
    @9
    ad2antrr
    #
    @76
    @103
    @92
    @3
    @74
    @103
    @42
    @3
    cI
    cB
    @63
    cU
    @21
    ffvelrnda
    adantrl
    adantr
    @44
    @84
    @94
    cB
    cY
    @78
    @53
    frlmsslsp.b
    @91
    @52
    @94
    eqid
    #
    @54
    lmod0vs
    syl2anc
    eqtrd
    @93
    @6
    @57
    @53
    @5
    wcel
    @104
    @3
    @57
    @75
    @92
    @61
    ad2antrr
    @7
    @5
    cY
    @53
    @54
    @10
    lss0cl
    syl2anc
    eqeltrd
    pm2.61dan
    eqeltrd
    expr
    ralrimiv
    vz
    cI
    @5
    @46
    ffnfv
    sylanbrc
    @43
    @46
    @53
    cfsupp
    wbr
    #
    @46
    @53
    csupp
    co
    #
    cfn
    wcel
    #
    @43
    @96
    cfn
    wcel
    #
    @107
    @96
    wss
    #
    @108
    @43
    @1
    @48
    @109
    @49
    @51
    @1
    @48
    wa
    @11
    c.0
    cB
    cR
    cY
    cI
    cV
    @11
    c.0
    frlmsslsp.y
    frlmsslsp.z
    frlmsslsp.b
    frlmbasfsupp
    fsuppimpd
    syl2anc
    @3
    @42
    @48
    @110
    @51
    @66
    cI
    cvv
    vx
    @46
    @96
    @53
    @66
    @62
    cI
    cvv
    @46
    wf
    @73
    cI
    @46
    dffn2
    sylib
    @66
    @27
    cI
    @96
    cdif
    wcel
    #
    wa
    #
    @27
    @46
    cfv
    #
    @27
    @11
    cfv
    #
    @27
    cU
    cfv
    #
    @44
    co
    #
    @94
    @115
    @44
    co
    #
    @53
    @112
    @68
    @37
    @1
    @30
    @113
    @116
    wceq
    @66
    @68
    @111
    @70
    adantr
    @3
    @37
    @48
    @111
    @39
    ad2antrr
    @0
    @1
    @2
    @48
    @111
    simpll2
    @111
    @30
    @66
    @27
    cI
    @96
    eldifi
    #
    adantl
    cI
    @44
    @11
    cU
    cV
    @27
    fnfvof
    syl22anc
    @112
    @114
    @94
    @115
    @44
    @112
    @114
    c.0
    @94
    @66
    cI
    @25
    cvv
    @11
    cV
    @96
    @27
    c.0
    @69
    @96
    @96
    wss
    @66
    @96
    ssid
    a1i
    @71
    @98
    @66
    @100
    a1i
    suppssr
    @3
    @101
    @48
    @111
    @102
    ad2antrr
    eqtrd
    oveq1d
    @112
    @6
    @115
    cB
    wcel
    #
    @117
    @53
    wceq
    @3
    @6
    @48
    @111
    @9
    ad2antrr
    @66
    @20
    @30
    @119
    @111
    @3
    @20
    @48
    @21
    adantr
    @118
    cI
    cB
    @27
    cU
    ffvelrn
    syl2an
    @44
    @84
    @94
    cB
    cY
    @115
    @53
    frlmsslsp.b
    @91
    @52
    @105
    @54
    lmod0vs
    syl2anc
    3eqtrd
    suppss
    syldan
    @96
    @107
    ssfi
    syl2anc
    @43
    @46
    wfun
    #
    @46
    cvv
    wcel
    @53
    cvv
    wcel
    #
    @106
    @108
    wb
    @43
    @62
    @120
    @43
    cI
    cI
    @44
    cI
    @11
    cU
    cV
    cV
    @43
    @11
    @25
    cI
    cmap
    co
    wcel
    #
    @68
    @3
    @1
    @48
    @122
    @42
    @0
    @1
    @2
    simp2
    @86
    cB
    cR
    cY
    cI
    @25
    cV
    @11
    frlmsslsp.y
    @26
    frlmsslsp.b
    frlmbasmap
    syl2an
    @11
    @25
    cI
    elmapfn
    syl
    @43
    @20
    @37
    @3
    @20
    @42
    @21
    adantr
    @38
    syl
    @49
    @49
    @72
    offn
    cI
    @46
    fnfun
    syl
    @43
    @11
    cU
    @45
    ovexd
    @121
    @43
    cY
    c0g
    fvex
    a1i
    @46
    cvv
    cvv
    @53
    funisfsupp
    syl3anc
    mpbird
    gsumsubgcl
    eqeltrd
    ex
    ssrdv
    eqssd
end
