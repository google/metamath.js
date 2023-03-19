include "c0.mm"
include "wceq.mm"
include "cof.mm"
include "co.mm"
include "cgsu.mm"
include "chash.mm"
include "cfv.mm"
include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "wa.mm"
include "cmnd.mm"
include "mndidcl.mm"
include "syl.mm"
include "mndlid.mm"
include "syl2anc.mm"
include "adantr.mm"
include "cmpt.mm"
include "cvv.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "csupp.mm"
include "cun.mm"
include "wf.mm"
include "fex.mm"
include "suppun.mm"
include "syl6sseqr.mm"
include "gsumcllem.mm"
include "oveq2d.mm"
include "gsumz.mm"
include "eqtrd.mm"
include "uncom.mm"
include "oveq1i.mm"
include "oveq12d.mm"
include "ad2antrr.mm"
include "offval2.mm"
include "mpteq2dv.mm"
include "3eqtr4rd.mm"
include "ex.mm"
include "ccom.mm"
include "cseq.mm"
include "mndcl.mm"
include "3expb.mm"
include "sylan.mm"
include "caovclg.mm"
include "cuz.mm"
include "simprl.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "wf1.mm"
include "wss.mm"
include "f1of1.mm"
include "ad2antll.mm"
include "cdm.mm"
include "suppssdm.mm"
include "dmun.mm"
include "fdm.mm"
include "uneq12d.mm"
include "unidm.mm"
include "syl6eq.mm"
include "syl5req.mm"
include "3sstr4d.mm"
include "f1ss.mm"
include "f1f.mm"
include "fco.mm"
include "ffvelrnda.mm"
include "ffnd.mm"
include "ovexd.mm"
include "inidm.mm"
include "ofco.mm"
include "fveq1d.mm"
include "wfn.mm"
include "fnfco.mm"
include "eqidd.mm"
include "ofval.mm"
include "cfzo.mm"
include "caddc.mm"
include "elfzouz.mm"
include "adantl.mm"
include "elfzouz2.mm"
include "fzss2.mm"
include "sselda.mm"
include "adantlr.mm"
include "syldan.mm"
include "seqcl.mm"
include "fzofzp1.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "cima.mm"
include "cres.mm"
include "csn.mm"
include "fvco3.mm"
include "cdif.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "wral.mm"
include "wi.mm"
include "wal.mm"
include "expr.mm"
include "ralrimiv.mm"
include "alrimiv.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "syl5ss.mm"
include "vex.mm"
include "imaex.mm"
include "sseq1.mm"
include "difeq2.mm"
include "reseq2.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "raleqbidv.mm"
include "imbi12d.mm"
include "spcv.mm"
include "sylc.mm"
include "fzp1nel.mm"
include "wb.mm"
include "f1elima.mm"
include "syl3anc.mm"
include "mtbiri.mm"
include "eldifd.mm"
include "rspcdva.mm"
include "eqeltrd.mm"
include "fssresd.mm"
include "resss.mm"
include "rnss.mm"
include "ax-mp.mm"
include "cntzidss.mm"
include "sylancl.mm"
include "syl6eleqr.mm"
include "f1ores.mm"
include "cin.mm"
include "dmres.mm"
include "syl5sseq.mm"
include "inss1.mm"
include "df-ima.mm"
include "sstrd.mm"
include "eqid.mm"
include "gsumval3.mm"
include "eqimss2i.mm"
include "cores.mm"
include "resco.mm"
include "eqtr4i.mm"
include "fveq1i.mm"
include "fvres.mm"
include "syl5eq.mm"
include "seqfveq.mm"
include "eqtr2d.mm"
include "elsn.mm"
include "sylibr.mm"
include "cntzi.mm"
include "eqcomd.mm"
include "mnd4g.mm"
include "seqcaopr3.mm"
include "ccnv.mm"
include "off.mm"
include "eldifi.mm"
include "sylan2.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "sseq2d.mm"
include "mpbird.mm"
include "suppssr.mm"
include "3eqtrd.mm"
include "suppss.mm"
include "ovex.mm"
include "coex.mm"
include "suppimacnv.mm"
include "mp2an.mm"
include "3eqtr4d.mm"
include "exlimdv.mm"
include "expimpd.mm"
include "cfn.mm"
include "wo.mm"
include "fsuppun.mm"
include "syl5eqel.mm"
include "fz1f1o.mm"
include "mpjaod.mm"

theorem gsumzaddlem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let cZ: class Z
  let vf: setvar f
  let vn: setvar n
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cS: class S
  assume gsumzadd.b: |- B = ( Base ` G )
  assume gsumzadd.0: |- .0. = ( 0g ` G )
  assume gsumzadd.p: |- .+ = ( +g ` G )
  assume gsumzadd.z: |- Z = ( Cntz ` G )
  assume gsumzadd.g: |- ( ph -> G e. Mnd )
  assume gsumzadd.a: |- ( ph -> A e. V )
  assume gsumzadd.fn: |- ( ph -> F finSupp .0. )
  assume gsumzadd.hn: |- ( ph -> H finSupp .0. )
  assume gsumzaddlem.w: |- W = ( ( F u. H ) supp .0. )
  assume gsumzaddlem.f: |- ( ph -> F : A --> B )
  assume gsumzaddlem.h: |- ( ph -> H : A --> B )
  assume gsumzaddlem.1: |- ( ph -> ran F C_ ( Z ` ran F ) )
  assume gsumzaddlem.2: |- ( ph -> ran H C_ ( Z ` ran H ) )
  assume gsumzaddlem.3: |- ( ph -> ran ( F oF .+ H ) C_ ( Z ` ran ( F oF .+ H ) ) )
  assume gsumzaddlem.4: |- ( ( ph /\ ( x C_ A /\ k e. ( A \ x ) ) ) -> ( F ` k ) e. ( Z ` { ( G gsum ( H |` x ) ) } ) )

  disjoint k x
  disjoint .+ k
  disjoint .+ x
  disjoint .0. k
  disjoint .0. x
  disjoint F k
  disjoint F x
  disjoint G k
  disjoint G x
  disjoint A k
  disjoint A x
  disjoint B k
  disjoint B x
  disjoint H k
  disjoint H x
  disjoint k ph
  disjoint ph x
  disjoint V x
  disjoint W k
  disjoint W x
  disjoint Z k
  disjoint Z x
  disjoint f k
  disjoint f n
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint .+ f
  disjoint k n
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint .+ n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint .+ w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint .+ y
  disjoint .+ z
  disjoint F f
  disjoint F n
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint G f
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint H f
  disjoint H n
  disjoint H w
  disjoint H y
  disjoint f ph
  disjoint n ph
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint S x
  disjoint S y
  disjoint W f
  disjoint W n
  disjoint W w
  disjoint W y
  disjoint W z
  assert |- ( ph -> ( G gsum ( F oF .+ H ) ) = ( ( G gsum F ) .+ ( G gsum H ) ) )

  proof
    wph
    cW
    c0
    wceq
    #
    cG
    cF
    cH
    c.pl
    cof
    #
    co
    #
    cgsu
    co
    #
    cG
    cF
    cgsu
    co
    #
    cG
    cH
    cgsu
    co
    #
    c.pl
    co
    #
    wceq
    #
    cW
    chash
    cfv
    #
    cn
    wcel
    #
    c1
    @8
    cfz
    co
    #
    cW
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    wa
    #
    wph
    @0
    @7
    wph
    @0
    wa
    #
    c.0
    c.0
    c.pl
    co
    #
    c.0
    @6
    @3
    wph
    @16
    c.0
    wceq
    #
    @0
    wph
    cG
    cmnd
    wcel
    #
    c.0
    cB
    wcel
    #
    @17
    gsumzadd.g
    wph
    @18
    @19
    gsumzadd.g
    cB
    cG
    c.0
    gsumzadd.b
    gsumzadd.0
    mndidcl
    syl
    #
    cB
    c.pl
    cG
    c.0
    c.0
    gsumzadd.b
    gsumzadd.p
    gsumzadd.0
    mndlid
    syl2anc
    #
    adantr
    #
    @15
    @4
    c.0
    @5
    c.0
    c.pl
    @15
    @4
    cG
    vx
    cA
    c.0
    cmpt
    #
    cgsu
    co
    #
    c.0
    @15
    cF
    @23
    cG
    cgsu
    wph
    cA
    cB
    cvv
    vx
    cF
    cV
    cW
    c.0
    gsumzaddlem.f
    gsumzadd.a
    c.0
    cvv
    wcel
    #
    wph
    c.0
    cG
    c0g
    cfv
    cvv
    gsumzadd.0
    cG
    c0g
    fvex
    eqeltri
    #
    a1i
    #
    wph
    cF
    c.0
    csupp
    co
    #
    cF
    cH
    cun
    #
    c.0
    csupp
    co
    #
    cW
    wph
    cF
    cH
    cvv
    c.0
    wph
    cA
    cB
    cH
    wf
    #
    cA
    cV
    wcel
    #
    cH
    cvv
    wcel
    gsumzaddlem.h
    gsumzadd.a
    cA
    cB
    cV
    cH
    fex
    syl2anc
    suppun
    #
    gsumzaddlem.w
    syl6sseqr
    gsumcllem
    #
    oveq2d
    wph
    @24
    c.0
    wceq
    #
    @0
    wph
    @18
    @32
    @35
    gsumzadd.g
    gsumzadd.a
    cA
    vx
    cG
    cV
    c.0
    gsumzadd.0
    gsumz
    syl2anc
    adantr
    #
    eqtrd
    @15
    @5
    @24
    c.0
    @15
    cH
    @23
    cG
    cgsu
    wph
    cA
    cB
    cvv
    vx
    cH
    cV
    cW
    c.0
    gsumzaddlem.h
    gsumzadd.a
    @27
    wph
    cH
    c.0
    csupp
    co
    #
    @30
    cW
    wph
    @37
    cH
    cF
    cun
    #
    c.0
    csupp
    co
    #
    @30
    wph
    cH
    cF
    cvv
    c.0
    wph
    cA
    cB
    cF
    wf
    #
    @32
    cF
    cvv
    wcel
    gsumzaddlem.f
    gsumzadd.a
    cA
    cB
    cV
    cF
    fex
    syl2anc
    suppun
    #
    @29
    @38
    c.0
    csupp
    cF
    cH
    uncom
    oveq1i
    #
    syl6sseqr
    gsumzaddlem.w
    syl6sseqr
    gsumcllem
    #
    oveq2d
    @36
    eqtrd
    oveq12d
    @15
    @3
    @24
    c.0
    @15
    @2
    @23
    cG
    cgsu
    @15
    @2
    vx
    cA
    @16
    cmpt
    @23
    @15
    vx
    cA
    c.0
    c.0
    c.pl
    cF
    cH
    cV
    cB
    cB
    wph
    @32
    @0
    gsumzadd.a
    adantr
    wph
    @19
    @0
    vx
    cv
    #
    cA
    wcel
    #
    @20
    ad2antrr
    #
    @46
    @34
    @43
    offval2
    @15
    vx
    cA
    @16
    c.0
    @22
    mpteq2dv
    eqtrd
    oveq2d
    @36
    eqtrd
    3eqtr4rd
    ex
    wph
    @9
    @13
    @7
    wph
    @9
    wa
    @12
    @7
    vf
    wph
    @9
    @12
    @7
    wph
    @9
    @12
    wa
    #
    wa
    #
    @8
    c.pl
    @2
    @11
    ccom
    #
    c1
    cseq
    cfv
    @8
    c.pl
    cF
    @11
    ccom
    #
    c1
    cseq
    #
    cfv
    #
    @8
    c.pl
    cH
    @11
    ccom
    #
    c1
    cseq
    #
    cfv
    #
    c.pl
    co
    @3
    @6
    @48
    vx
    vy
    c.pl
    c.pl
    cB
    vk
    vn
    @50
    @53
    @49
    c1
    @8
    @48
    vz
    vw
    @44
    vy
    cv
    cB
    cB
    cB
    c.pl
    @48
    @18
    vz
    cv
    #
    cB
    wcel
    #
    vw
    cv
    #
    cB
    wcel
    #
    wa
    @56
    @58
    c.pl
    co
    cB
    wcel
    #
    wph
    @18
    @47
    gsumzadd.g
    adantr
    #
    @18
    @57
    @59
    @60
    cB
    c.pl
    cG
    @56
    @58
    gsumzadd.b
    gsumzadd.p
    mndcl
    3expb
    sylan
    #
    caovclg
    #
    @63
    @48
    @8
    cn
    c1
    cuz
    cfv
    #
    wph
    @9
    @12
    simprl
    #
    nnuz
    syl6eleq
    @48
    @10
    cB
    vk
    cv
    #
    @50
    @48
    @40
    @10
    cA
    @11
    wf
    #
    @10
    cB
    @50
    wf
    #
    wph
    @40
    @47
    gsumzaddlem.f
    adantr
    #
    @48
    @10
    cA
    @11
    wf1
    #
    @67
    @48
    @10
    cW
    @11
    wf1
    #
    cW
    cA
    wss
    #
    @70
    @12
    @71
    wph
    @9
    @10
    cW
    @11
    f1of1
    ad2antll
    wph
    @72
    @47
    wph
    @30
    @29
    cdm
    #
    cW
    cA
    @30
    @73
    wss
    wph
    @29
    c.0
    suppssdm
    a1i
    cW
    @30
    wceq
    wph
    gsumzaddlem.w
    a1i
    wph
    @73
    cF
    cdm
    #
    cH
    cdm
    #
    cun
    #
    cA
    cF
    cH
    dmun
    wph
    @76
    cA
    cA
    cun
    cA
    wph
    @74
    cA
    @75
    cA
    wph
    @40
    @74
    cA
    wceq
    gsumzaddlem.f
    cA
    cB
    cF
    fdm
    syl
    wph
    @31
    @75
    cA
    wceq
    gsumzaddlem.h
    cA
    cB
    cH
    fdm
    syl
    uneq12d
    cA
    unidm
    syl6eq
    syl5req
    3sstr4d
    adantr
    @10
    cW
    cA
    @11
    f1ss
    syl2anc
    #
    @10
    cA
    @11
    f1f
    syl
    #
    @10
    cA
    cB
    cF
    @11
    fco
    syl2anc
    #
    ffvelrnda
    #
    @48
    @10
    cB
    @66
    @53
    @48
    @31
    @67
    @10
    cB
    @53
    wf
    #
    wph
    @31
    @47
    gsumzaddlem.h
    adantr
    #
    @78
    @10
    cA
    cB
    cH
    @11
    fco
    syl2anc
    #
    ffvelrnda
    #
    @48
    @66
    @10
    wcel
    #
    wa
    #
    @66
    @49
    cfv
    #
    @66
    @50
    @53
    @1
    co
    #
    cfv
    #
    @66
    @50
    cfv
    #
    @66
    @53
    cfv
    #
    c.pl
    co
    @48
    @87
    @89
    wceq
    @85
    @48
    @66
    @49
    @88
    @48
    cA
    cA
    cA
    @10
    c.pl
    cF
    cH
    @11
    cV
    cV
    cvv
    @48
    cA
    cB
    cF
    @69
    ffnd
    #
    @48
    cA
    cB
    cH
    @82
    ffnd
    #
    @78
    wph
    @32
    @47
    gsumzadd.a
    adantr
    #
    @94
    @48
    c1
    @8
    cfz
    ovexd
    #
    cA
    inidm
    #
    ofco
    fveq1d
    adantr
    @48
    @10
    @10
    @90
    @91
    c.pl
    @10
    @50
    @53
    cvv
    cvv
    @66
    @48
    cF
    cA
    wfn
    @67
    @50
    @10
    wfn
    @92
    @78
    cA
    @10
    cF
    @11
    fnfco
    syl2anc
    @48
    cH
    cA
    wfn
    @67
    @53
    @10
    wfn
    @93
    @78
    cA
    @10
    cH
    @11
    fnfco
    syl2anc
    @95
    @95
    @10
    inidm
    @86
    @90
    eqidd
    @86
    @91
    eqidd
    ofval
    eqtrd
    @48
    vn
    cv
    #
    c1
    @8
    cfzo
    co
    wcel
    #
    wa
    #
    cB
    c.pl
    cG
    @97
    c1
    caddc
    co
    #
    @53
    cfv
    #
    @97
    @51
    cfv
    @97
    @54
    cfv
    #
    @100
    @50
    cfv
    #
    gsumzadd.b
    gsumzadd.p
    wph
    @18
    @47
    @98
    gsumzadd.g
    ad2antrr
    #
    @99
    vk
    vx
    c.pl
    cB
    @50
    c1
    @97
    @98
    @97
    @64
    wcel
    @48
    @97
    c1
    @8
    elfzouz
    adantl
    #
    @99
    @66
    c1
    @97
    cfz
    co
    #
    wcel
    #
    @85
    @90
    cB
    wcel
    #
    @99
    @106
    @10
    @66
    @99
    @8
    @97
    cuz
    cfv
    wcel
    #
    @106
    @10
    wss
    #
    @98
    @109
    @48
    @97
    c1
    @8
    elfzouz2
    adantl
    @97
    c1
    @8
    fzss2
    syl
    #
    sselda
    #
    @48
    @85
    @108
    @98
    @80
    adantlr
    syldan
    @99
    @18
    @66
    cB
    wcel
    #
    @44
    cB
    wcel
    #
    wa
    #
    @66
    @44
    c.pl
    co
    cB
    wcel
    #
    @104
    @18
    @113
    @114
    @116
    cB
    c.pl
    cG
    @66
    @44
    gsumzadd.b
    gsumzadd.p
    mndcl
    3expb
    #
    sylan
    #
    seqcl
    @99
    vk
    vx
    c.pl
    cB
    @53
    c1
    @97
    @105
    @99
    @107
    @85
    @91
    cB
    wcel
    #
    @112
    @48
    @85
    @119
    @98
    @84
    adantlr
    syldan
    @118
    seqcl
    @48
    @68
    @100
    @10
    wcel
    #
    @103
    cB
    wcel
    @98
    @79
    c1
    @8
    @97
    fzofzp1
    #
    @10
    cB
    @100
    @50
    ffvelrn
    syl2an
    @48
    @81
    @120
    @101
    cB
    wcel
    @98
    @83
    @121
    @10
    cB
    @100
    @53
    ffvelrn
    syl2an
    @99
    @103
    @102
    c.pl
    co
    #
    @102
    @103
    c.pl
    co
    #
    @99
    @103
    cG
    cH
    @11
    @106
    cima
    #
    cres
    #
    cgsu
    co
    #
    csn
    #
    cZ
    cfv
    #
    wcel
    @102
    @127
    wcel
    #
    @122
    @123
    wceq
    @99
    @103
    @100
    @11
    cfv
    #
    cF
    cfv
    #
    @128
    @48
    @67
    @120
    @103
    @131
    wceq
    @98
    @78
    @121
    @10
    cA
    @100
    cF
    @11
    fvco3
    syl2an
    @99
    @66
    cF
    cfv
    #
    @128
    wcel
    #
    @131
    @128
    wcel
    vk
    cA
    @124
    cdif
    #
    @130
    @66
    @130
    wceq
    @132
    @131
    @128
    @66
    @130
    cF
    fveq2
    eleq1d
    @99
    @44
    cA
    wss
    #
    @132
    cG
    cH
    @44
    cres
    #
    cgsu
    co
    #
    csn
    #
    cZ
    cfv
    #
    wcel
    #
    vk
    cA
    @44
    cdif
    #
    wral
    #
    wi
    #
    vx
    wal
    #
    @124
    cA
    wss
    #
    @133
    vk
    @134
    wral
    #
    wph
    @144
    @47
    @98
    wph
    @143
    vx
    wph
    @135
    @142
    wph
    @135
    wa
    @140
    vk
    @141
    wph
    @135
    @66
    @141
    wcel
    @140
    gsumzaddlem.4
    expr
    ralrimiv
    ex
    alrimiv
    ad2antrr
    @99
    @124
    @11
    crn
    #
    cA
    @11
    @106
    imassrn
    @99
    @67
    @147
    cA
    wss
    @48
    @67
    @98
    @78
    adantr
    @10
    cA
    @11
    frn
    syl
    syl5ss
    #
    @143
    @145
    @146
    wi
    vx
    @124
    @11
    @106
    vf
    vex
    #
    imaex
    #
    @44
    @124
    wceq
    #
    @135
    @145
    @142
    @146
    @44
    @124
    cA
    sseq1
    @151
    @140
    @133
    vk
    @141
    @134
    @44
    @124
    cA
    difeq2
    @151
    @139
    @128
    @132
    @151
    @138
    @127
    cZ
    @151
    @137
    @126
    @151
    @136
    @125
    cG
    cgsu
    @44
    @124
    cH
    reseq2
    oveq2d
    sneqd
    fveq2d
    eleq2d
    raleqbidv
    imbi12d
    spcv
    sylc
    @99
    @130
    cA
    @124
    @48
    @67
    @120
    @130
    cA
    wcel
    @98
    @78
    @121
    @10
    cA
    @100
    @11
    ffvelrn
    syl2an
    @99
    @130
    @124
    wcel
    #
    @100
    @106
    wcel
    #
    c1
    @97
    fzp1nel
    @99
    @70
    @120
    @110
    @152
    @153
    wb
    @48
    @70
    @98
    @77
    adantr
    #
    @98
    @120
    @48
    @121
    adantl
    @111
    @10
    cA
    @11
    @100
    @106
    f1elima
    syl3anc
    mtbiri
    eldifd
    rspcdva
    eqeltrd
    @99
    @102
    @126
    wceq
    @129
    @99
    @126
    @97
    c.pl
    @125
    @11
    @106
    cres
    #
    ccom
    #
    c1
    cseq
    cfv
    @102
    @99
    @124
    cB
    c.pl
    @125
    cG
    @155
    @97
    cvv
    @156
    c.0
    csupp
    co
    #
    c.0
    cZ
    gsumzadd.b
    gsumzadd.0
    gsumzadd.p
    gsumzadd.z
    @104
    @124
    cvv
    wcel
    @99
    @150
    a1i
    @99
    cA
    cB
    @124
    cH
    wph
    @31
    @47
    @98
    gsumzaddlem.h
    ad2antrr
    @148
    fssresd
    @99
    cH
    crn
    #
    @158
    cZ
    cfv
    wss
    #
    @125
    crn
    #
    @158
    wss
    #
    @160
    @160
    cZ
    cfv
    wss
    wph
    @159
    @47
    @98
    gsumzaddlem.2
    ad2antrr
    @125
    cH
    wss
    @161
    cH
    @124
    resss
    @125
    cH
    rnss
    ax-mp
    @158
    @160
    cG
    cZ
    gsumzadd.z
    cntzidss
    sylancl
    @99
    @97
    @64
    cn
    @105
    nnuz
    syl6eleqr
    @99
    @106
    @124
    @155
    wf1o
    #
    @106
    @124
    @155
    wf1
    @99
    @70
    @110
    @162
    @154
    @111
    @10
    cA
    @106
    @11
    f1ores
    syl2anc
    @106
    @124
    @155
    f1of1
    syl
    @99
    @125
    c.0
    csupp
    co
    #
    @124
    @75
    cin
    #
    @155
    crn
    #
    @99
    @125
    cdm
    #
    @163
    @164
    @125
    c.0
    suppssdm
    @166
    @164
    wceq
    @99
    cH
    @124
    dmres
    a1i
    syl5sseq
    @99
    @124
    @164
    @165
    @124
    @75
    inss1
    @124
    @165
    wceq
    @99
    @11
    @106
    df-ima
    #
    a1i
    syl5sseq
    sstrd
    @157
    eqid
    gsumval3
    @99
    c.pl
    vk
    @156
    @53
    c1
    @97
    @105
    @107
    @66
    @156
    cfv
    #
    @91
    wceq
    @99
    @107
    @168
    @66
    @53
    @106
    cres
    #
    cfv
    @91
    @66
    @156
    @169
    @156
    cH
    @155
    ccom
    #
    @169
    @165
    @124
    wss
    @156
    @170
    wceq
    @124
    @165
    @167
    eqimss2i
    cH
    @155
    @124
    cores
    ax-mp
    cH
    @11
    @106
    resco
    eqtr4i
    fveq1i
    @66
    @106
    @53
    fvres
    syl5eq
    adantl
    seqfveq
    eqtr2d
    @102
    @126
    @97
    @54
    fvex
    elsn
    sylibr
    c.pl
    @127
    cG
    @103
    @102
    cZ
    gsumzadd.p
    gsumzadd.z
    cntzi
    syl2anc
    eqcomd
    mnd4g
    seqcaopr3
    @48
    cA
    cB
    c.pl
    @2
    cG
    @11
    @8
    cV
    @49
    ccnv
    cvv
    c.0
    csn
    cdif
    cima
    #
    c.0
    cZ
    gsumzadd.b
    gsumzadd.0
    gsumzadd.p
    gsumzadd.z
    @61
    @94
    @48
    vz
    vw
    cA
    cA
    cA
    c.pl
    cB
    cB
    cB
    cF
    cH
    cV
    cV
    @62
    @69
    @82
    @94
    @94
    @96
    off
    wph
    @2
    crn
    #
    @172
    cZ
    cfv
    wss
    @47
    gsumzaddlem.3
    adantr
    @65
    @77
    @48
    cA
    cB
    vx
    @2
    @147
    c.0
    @48
    vk
    vx
    cA
    cA
    cA
    c.pl
    cB
    cB
    cB
    cF
    cH
    cV
    cV
    @48
    @18
    @115
    @116
    @61
    @117
    sylan
    @69
    @82
    @94
    @94
    @96
    off
    @48
    @44
    cA
    @147
    cdif
    wcel
    #
    wa
    #
    @44
    @2
    cfv
    #
    @44
    cF
    cfv
    #
    @44
    cH
    cfv
    #
    c.pl
    co
    #
    @16
    c.0
    @173
    @48
    @45
    @175
    @178
    wceq
    @44
    cA
    @147
    eldifi
    @48
    cA
    cA
    @176
    @177
    c.pl
    cA
    cF
    cH
    cV
    cV
    @44
    @92
    @93
    @94
    @94
    @96
    @48
    @45
    wa
    #
    @176
    eqidd
    @179
    @177
    eqidd
    ofval
    sylan2
    @174
    @176
    c.0
    @177
    c.0
    c.pl
    @48
    cA
    cB
    cvv
    cF
    cV
    @147
    @44
    c.0
    @69
    @48
    @28
    @147
    wss
    #
    @28
    @30
    wss
    #
    wph
    @181
    @47
    @33
    adantr
    @12
    @180
    @181
    wb
    wph
    @9
    @12
    @147
    @30
    @28
    @12
    @147
    cW
    @30
    @12
    @10
    cW
    @11
    wfo
    @147
    cW
    wceq
    @10
    cW
    @11
    f1ofo
    @10
    cW
    @11
    forn
    syl
    gsumzaddlem.w
    syl6eq
    #
    sseq2d
    ad2antll
    mpbird
    #
    @94
    @25
    @48
    @26
    a1i
    #
    suppssr
    @48
    cA
    cB
    cvv
    cH
    cV
    @147
    @44
    c.0
    @82
    @48
    @37
    @147
    wss
    #
    @37
    @30
    wss
    #
    @48
    @37
    @39
    @30
    wph
    @37
    @39
    wss
    @47
    @41
    adantr
    @42
    syl6sseqr
    @12
    @185
    @186
    wb
    wph
    @9
    @12
    @147
    @30
    @37
    @182
    sseq2d
    ad2antll
    mpbird
    #
    @94
    @184
    suppssr
    oveq12d
    wph
    @17
    @47
    @173
    @21
    ad2antrr
    3eqtrd
    suppss
    @49
    cvv
    wcel
    #
    @25
    @171
    @49
    c.0
    csupp
    co
    #
    wceq
    @2
    @11
    cF
    cH
    @1
    ovex
    @149
    coex
    @26
    @188
    @25
    wa
    @189
    @171
    @49
    cvv
    cvv
    c.0
    suppimacnv
    eqcomd
    mp2an
    gsumval3
    @48
    @4
    @52
    @5
    @55
    c.pl
    @48
    cA
    cB
    c.pl
    cF
    cG
    @11
    @8
    cV
    @50
    c.0
    csupp
    co
    #
    c.0
    cZ
    gsumzadd.b
    gsumzadd.0
    gsumzadd.p
    gsumzadd.z
    @61
    @94
    @69
    wph
    cF
    crn
    #
    @191
    cZ
    cfv
    wss
    @47
    gsumzaddlem.1
    adantr
    @65
    @77
    @183
    @190
    eqid
    gsumval3
    @48
    cA
    cB
    c.pl
    cH
    cG
    @11
    @8
    cV
    @53
    c.0
    csupp
    co
    #
    c.0
    cZ
    gsumzadd.b
    gsumzadd.0
    gsumzadd.p
    gsumzadd.z
    @61
    @94
    @82
    wph
    @159
    @47
    gsumzaddlem.2
    adantr
    @65
    @77
    @187
    @192
    eqid
    gsumval3
    oveq12d
    3eqtr4d
    expr
    exlimdv
    expimpd
    wph
    cW
    cfn
    wcel
    @0
    @14
    wo
    wph
    cW
    @30
    cfn
    gsumzaddlem.w
    wph
    cF
    cH
    c.0
    gsumzadd.fn
    gsumzadd.hn
    fsuppun
    syl5eqel
    cW
    vf
    fz1f1o
    syl
    mpjaod
end
