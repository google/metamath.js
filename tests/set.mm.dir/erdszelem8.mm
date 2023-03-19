include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "chash.mm"
include "wceq.mm"
include "cima.mm"
include "clt.mm"
include "cres.mm"
include "wiso.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cpw.mm"
include "crab.mm"
include "wrex.mm"
include "wne.mm"
include "wi.mm"
include "wfun.mm"
include "cvv.mm"
include "cn0.mm"
include "cpnf.mm"
include "csn.mm"
include "cun.mm"
include "wf.mm"
include "hashf.mm"
include "ffun.mm"
include "ax-mp.mm"
include "erdszelem5.mm"
include "mpdan.mm"
include "fvelima.mm"
include "sylancr.mm"
include "wss.mm"
include "w3a.mm"
include "eqid.mm"
include "erdszelem1.mm"
include "cfn.mm"
include "fzfid.mm"
include "simplr1.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "hashcl.mm"
include "syl.mm"
include "nn0red.mm"
include "caddc.mm"
include "cle.mm"
include "cr.mm"
include "csup.mm"
include "c0.mm"
include "wral.mm"
include "cn.mm"
include "erdszelem2.mm"
include "simpri.mm"
include "nnssre.mm"
include "sstri.mm"
include "a1i.mm"
include "wn.mm"
include "elfznn.mm"
include "nnred.mm"
include "ltnled.mm"
include "mpbid.mm"
include "elfzle2.mm"
include "nsyl.mm"
include "ad2antrr.mm"
include "ssneldd.mm"
include "hashunsng.mm"
include "mp2and.mm"
include "cuz.mm"
include "cz.mm"
include "elfzelz.mm"
include "ltled.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "fzss2.mm"
include "sstrd.mm"
include "elfz1end.mm"
include "sylib.mm"
include "snssd.mm"
include "unssd.mm"
include "simplr2.mm"
include "wb.mm"
include "wf1.mm"
include "f1f.mm"
include "elfzuz3.mm"
include "3syl.mm"
include "wor.mm"
include "fzssuz.mm"
include "uzssz.mm"
include "zssre.mm"
include "ltso.mm"
include "soss.mm"
include "mp2.mm"
include "soisores.mm"
include "mpanl12.mm"
include "r19.21bi.mm"
include "sselda.mm"
include "sseldi.mm"
include "ad3antrrr.mm"
include "lenltd.mm"
include "adantr.mm"
include "simplr3.mm"
include "simpr.mm"
include "isorel.mm"
include "fvres.mm"
include "breqan12d.mm"
include "adantl.mm"
include "bitrd.mm"
include "syl12anc.mm"
include "mtbid.mm"
include "simplr.mm"
include "ffvelrnd.mm"
include "sotr2.mm"
include "mpan.mm"
include "syl3anc.mm"
include "a1d.mm"
include "elsni.mm"
include "fveq2d.mm"
include "breq2d.mm"
include "imbi2d.mm"
include "syl5ibrcom.mm"
include "ralrimiv.mm"
include "ralunb.mm"
include "sylanbrc.mm"
include "ralrimiva.mm"
include "zred.mm"
include "syldan.mm"
include "pm2.21d.mm"
include "breq1d.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "mpbird.mm"
include "ssun2.mm"
include "snssg.mm"
include "mpbiri.mm"
include "cdm.mm"
include "vex.mm"
include "snex.mm"
include "unex.mm"
include "fdmi.mm"
include "eleqtrri.mm"
include "funfvima.mm"
include "mp2an.mm"
include "eqeltrrd.mm"
include "ne0i.mm"
include "simpli.mm"
include "fimaxre2.mm"
include "sylancl.mm"
include "suprub.mm"
include "syl31anc.mm"
include "erdszelem3.mm"
include "breqtrrd.mm"
include "erdszelem6.mm"
include "nnnn0d.mm"
include "nn0ltp1le.mm"
include "ltned.mm"
include "ex.mm"
include "neeq1.mm"
include "syl5ibcom.mm"
include "sylan2b.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "necon2bd.mm"

theorem erdszelem8
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cK: class K
  let cN: class N
  let cO: class O
  let vf: setvar f
  let vw: setvar w
  let vz: setvar z
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let cI: class I
  let cJ: class J
  let cR: class R
  let va: setvar a
  let vb: setvar b
  let cS: class S
  let cT: class T
  assume erdsze.n: |- ( ph -> N e. NN )
  assume erdsze.f: |- ( ph -> F : ( 1 ... N ) -1-1-> RR )
  assume erdszelem.k: |- K = ( x e. ( 1 ... N ) |-> sup ( ( # " { y e. ~P ( 1 ... x ) | ( ( F |` y ) Isom < , O ( y , ( F " y ) ) /\ x e. y ) } ) , RR , < ) )
  assume erdszelem.o: |- O Or RR
  assume erdszelem.a: |- ( ph -> A e. ( 1 ... N ) )
  assume erdszelem.b: |- ( ph -> B e. ( 1 ... N ) )
  assume erdszelem.l: |- ( ph -> A < B )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint A x
  disjoint A y
  disjoint O x
  disjoint O y
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint f m
  disjoint f n
  disjoint f s
  disjoint F f
  disjoint m n
  disjoint m s
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n s
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint F s
  disjoint F w
  disjoint F z
  disjoint I n
  disjoint I s
  disjoint I x
  disjoint I y
  disjoint K f
  disjoint K s
  disjoint K z
  disjoint A f
  disjoint A s
  disjoint A w
  disjoint A z
  disjoint J n
  disjoint J s
  disjoint J x
  disjoint J y
  disjoint O f
  disjoint O s
  disjoint O w
  disjoint O z
  disjoint R m
  disjoint R s
  disjoint R x
  disjoint R y
  disjoint a b
  disjoint a m
  disjoint a n
  disjoint a s
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint N a
  disjoint b m
  disjoint b n
  disjoint b s
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint N b
  disjoint N m
  disjoint N n
  disjoint N s
  disjoint N w
  disjoint N z
  disjoint a f
  disjoint a ph
  disjoint b f
  disjoint b ph
  disjoint f ph
  disjoint m ph
  disjoint n ph
  disjoint ph s
  disjoint ph w
  disjoint ph z
  disjoint S m
  disjoint S s
  disjoint S x
  disjoint S y
  disjoint T a
  disjoint T b
  disjoint T m
  disjoint T s
  disjoint T w
  disjoint T z
  assert |- ( ph -> ( ( K ` A ) = ( K ` B ) -> -. ( F ` A ) O ( F ` B ) ) )

  proof
    wph
    cA
    cF
    cfv
    #
    cB
    cF
    cfv
    #
    cO
    wbr
    #
    cA
    cK
    cfv
    #
    cB
    cK
    cfv
    #
    wph
    vf
    cv
    #
    chash
    cfv
    #
    @3
    wceq
    #
    vf
    vy
    cv
    #
    cF
    @8
    cima
    clt
    cO
    cF
    @8
    cres
    wiso
    #
    cA
    @8
    wcel
    wa
    vy
    c1
    cA
    cfz
    co
    #
    cpw
    crab
    #
    wrex
    #
    @2
    @3
    @4
    wne
    #
    wi
    #
    wph
    chash
    wfun
    #
    @3
    chash
    @11
    cima
    wcel
    #
    @12
    cvv
    cn0
    cpnf
    csn
    cun
    #
    chash
    wf
    @15
    hashf
    cvv
    @17
    chash
    ffun
    ax-mp
    #
    wph
    cA
    c1
    cN
    cfz
    co
    #
    wcel
    #
    @16
    erdszelem.a
    wph
    vx
    vy
    cA
    cF
    cK
    cN
    cO
    erdsze.n
    erdsze.f
    erdszelem.k
    erdszelem.o
    erdszelem5
    mpdan
    vf
    @3
    @11
    chash
    fvelima
    sylancr
    wph
    @7
    @14
    vf
    @11
    @5
    @11
    wcel
    wph
    @5
    @10
    wss
    #
    @5
    cF
    @5
    cima
    #
    clt
    cO
    cF
    @5
    cres
    #
    wiso
    #
    cA
    @5
    wcel
    #
    w3a
    #
    @7
    @14
    wi
    vy
    cA
    @11
    cF
    cO
    @5
    @11
    eqid
    erdszelem1
    wph
    @26
    wa
    #
    @2
    @6
    @4
    wne
    #
    wi
    @7
    @14
    @27
    @2
    @28
    @27
    @2
    wa
    #
    @6
    @4
    @29
    @6
    @29
    @5
    cfn
    wcel
    #
    @6
    cn0
    wcel
    #
    @29
    @10
    cfn
    wcel
    @21
    @30
    @29
    c1
    cA
    fzfid
    @21
    @24
    @25
    wph
    @2
    simplr1
    #
    @10
    @5
    ssfi
    syl2anc
    #
    @5
    hashcl
    syl
    #
    nn0red
    @29
    @6
    @4
    clt
    wbr
    #
    @6
    c1
    caddc
    co
    #
    @4
    cle
    wbr
    #
    @29
    @36
    chash
    @9
    cB
    @8
    wcel
    wa
    vy
    c1
    cB
    cfz
    co
    #
    cpw
    crab
    #
    cima
    #
    cr
    clt
    csup
    #
    @4
    cle
    @29
    @40
    cr
    wss
    #
    @40
    c0
    wne
    #
    vw
    cv
    #
    vz
    cv
    #
    cle
    wbr
    vw
    @40
    wral
    vz
    cr
    wrex
    #
    @36
    @40
    wcel
    #
    @36
    @41
    cle
    wbr
    @42
    @29
    @40
    cn
    cr
    @40
    cfn
    wcel
    #
    @40
    cn
    wss
    #
    vy
    cB
    @39
    cF
    cO
    @39
    eqid
    #
    erdszelem2
    #
    simpri
    nnssre
    sstri
    a1i
    #
    @29
    @47
    @43
    @29
    @5
    cB
    csn
    #
    cun
    #
    chash
    cfv
    #
    @36
    @40
    @29
    @30
    cB
    @5
    wcel
    wn
    #
    @55
    @36
    wceq
    #
    @33
    @29
    @5
    @10
    cB
    @32
    wph
    cB
    @10
    wcel
    #
    wn
    @26
    @2
    wph
    cB
    cA
    cle
    wbr
    #
    @58
    wph
    cA
    cB
    clt
    wbr
    @59
    wn
    erdszelem.l
    wph
    cA
    cB
    wph
    cA
    wph
    @20
    cA
    cn
    wcel
    #
    erdszelem.a
    cA
    cN
    elfznn
    #
    syl
    nnred
    #
    wph
    cB
    wph
    cB
    @19
    wcel
    #
    cB
    cn
    wcel
    #
    erdszelem.b
    cB
    cN
    elfznn
    syl
    #
    nnred
    #
    ltnled
    mpbid
    cB
    c1
    cA
    elfzle2
    nsyl
    ad2antrr
    ssneldd
    @29
    @63
    @30
    @56
    wa
    @57
    wi
    wph
    @63
    @26
    @2
    erdszelem.b
    ad2antrr
    #
    @5
    cB
    @19
    hashunsng
    syl
    mp2and
    @29
    @54
    @39
    wcel
    #
    @55
    @40
    wcel
    #
    @29
    @54
    @38
    wss
    @54
    cF
    @54
    cima
    clt
    cO
    cF
    @54
    cres
    wiso
    #
    cB
    @54
    wcel
    #
    @68
    @29
    @5
    @53
    @38
    @29
    @5
    @10
    @38
    @32
    wph
    @10
    @38
    wss
    #
    @26
    @2
    wph
    cB
    cA
    cuz
    cfv
    #
    wcel
    #
    @72
    wph
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cA
    cB
    cle
    wbr
    @74
    wph
    @20
    @75
    erdszelem.a
    cA
    c1
    cN
    elfzelz
    syl
    wph
    @63
    @76
    erdszelem.b
    cB
    c1
    cN
    elfzelz
    syl
    wph
    cA
    cB
    @62
    @66
    erdszelem.l
    ltled
    cA
    cB
    eluz2
    syl3anbrc
    cA
    c1
    cB
    fzss2
    syl
    ad2antrr
    sstrd
    @29
    cB
    @38
    wph
    cB
    @38
    wcel
    #
    @26
    @2
    wph
    @64
    @77
    @65
    cB
    elfz1end
    sylib
    ad2antrr
    #
    snssd
    unssd
    #
    @29
    @70
    @45
    @44
    clt
    wbr
    #
    @45
    cF
    cfv
    #
    @44
    cF
    cfv
    #
    cO
    wbr
    #
    wi
    #
    vw
    @54
    wral
    #
    vz
    @54
    wral
    #
    @29
    @85
    vz
    @5
    wral
    @85
    vz
    @53
    wral
    @86
    @29
    @85
    vz
    @5
    @29
    @45
    @5
    wcel
    #
    wa
    #
    @84
    vw
    @5
    wral
    #
    @84
    vw
    @53
    wral
    @85
    @29
    @89
    vz
    @5
    @29
    @24
    @89
    vz
    @5
    wral
    #
    @21
    @24
    @25
    wph
    @2
    simplr2
    #
    @29
    @19
    cr
    cF
    wf
    #
    @5
    @19
    wss
    #
    @24
    @90
    wb
    #
    wph
    @92
    @26
    @2
    wph
    @19
    cr
    cF
    wf1
    @92
    erdsze.f
    @19
    cr
    cF
    f1f
    syl
    ad2antrr
    #
    @29
    @5
    @10
    @19
    @32
    wph
    @10
    @19
    wss
    #
    @26
    @2
    wph
    @20
    cN
    @73
    wcel
    @96
    erdszelem.a
    cA
    c1
    cN
    elfzuz3
    cA
    c1
    cN
    fzss2
    3syl
    ad2antrr
    sstrd
    #
    @19
    clt
    wor
    #
    cr
    cO
    wor
    #
    @92
    @93
    wa
    @94
    @19
    cr
    wss
    cr
    clt
    wor
    @98
    @19
    c1
    cuz
    cfv
    #
    cr
    c1
    cN
    fzssuz
    @100
    cz
    cr
    c1
    uzssz
    zssre
    sstri
    sstri
    #
    ltso
    @19
    cr
    clt
    soss
    mp2
    #
    erdszelem.o
    vz
    vw
    @5
    @19
    cr
    clt
    cO
    cF
    soisores
    mpanl12
    syl2anc
    mpbid
    r19.21bi
    @88
    @84
    vw
    @53
    @88
    @84
    @44
    @53
    wcel
    #
    @80
    @81
    @1
    cO
    wbr
    #
    wi
    @88
    @104
    @80
    @88
    @0
    @81
    cO
    wbr
    #
    wn
    #
    @2
    @104
    @88
    cA
    @45
    clt
    wbr
    #
    @105
    @88
    @45
    cA
    cle
    wbr
    #
    @107
    wn
    @88
    @45
    @10
    wcel
    @108
    @29
    @5
    @10
    @45
    @32
    sselda
    @45
    c1
    cA
    elfzle2
    syl
    @88
    @45
    cA
    @88
    @19
    cr
    @45
    @101
    @29
    @5
    @19
    @45
    @97
    sselda
    #
    sseldi
    @88
    cA
    @88
    @20
    @60
    wph
    @20
    @26
    @2
    @87
    erdszelem.a
    ad3antrrr
    #
    @61
    syl
    nnred
    lenltd
    mpbid
    @88
    @24
    @25
    @87
    @107
    @105
    wb
    @29
    @24
    @87
    @91
    adantr
    @29
    @25
    @87
    @21
    @24
    @25
    wph
    @2
    simplr3
    adantr
    @29
    @87
    simpr
    @24
    @25
    @87
    wa
    #
    wa
    @107
    cA
    @23
    cfv
    #
    @45
    @23
    cfv
    #
    cO
    wbr
    #
    @105
    @5
    @22
    cA
    @45
    clt
    cO
    @23
    isorel
    @111
    @114
    @105
    wb
    @24
    @25
    @87
    @112
    @0
    @113
    @81
    cO
    cA
    @5
    cF
    fvres
    @45
    @5
    cF
    fvres
    breqan12d
    adantl
    bitrd
    syl12anc
    mtbid
    @27
    @2
    @87
    simplr
    @88
    @81
    cr
    wcel
    #
    @0
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    @106
    @2
    wa
    @104
    wi
    #
    @88
    @19
    cr
    @45
    cF
    @29
    @92
    @87
    @95
    adantr
    #
    @109
    ffvelrnd
    @88
    @19
    cr
    cA
    cF
    @119
    @110
    ffvelrnd
    @88
    @19
    cr
    cB
    cF
    @119
    @29
    @63
    @87
    @67
    adantr
    ffvelrnd
    @99
    @115
    @116
    @117
    w3a
    @118
    erdszelem.o
    cr
    @81
    @0
    @1
    cO
    sotr2
    mpan
    syl3anc
    mp2and
    a1d
    @103
    @83
    @104
    @80
    @103
    @82
    @1
    @81
    cO
    @103
    @44
    cB
    cF
    @44
    cB
    elsni
    fveq2d
    breq2d
    imbi2d
    syl5ibrcom
    ralrimiv
    @84
    vw
    @5
    @53
    ralunb
    sylanbrc
    ralrimiva
    @29
    @85
    vz
    @53
    @29
    @85
    @45
    @53
    wcel
    #
    cB
    @44
    clt
    wbr
    #
    @83
    wi
    #
    vw
    @54
    wral
    @29
    @122
    vw
    @54
    @29
    @44
    @54
    wcel
    #
    wa
    @121
    @83
    @29
    @123
    @44
    @38
    wcel
    #
    @121
    wn
    #
    @29
    @54
    @38
    @44
    @79
    sselda
    @29
    @124
    wa
    #
    @44
    cB
    cle
    wbr
    #
    @125
    @124
    @127
    @29
    @44
    c1
    cB
    elfzle2
    adantl
    @126
    @44
    cB
    @124
    @44
    cr
    wcel
    @29
    @124
    @44
    @44
    c1
    cB
    elfzelz
    zred
    adantl
    wph
    cB
    cr
    wcel
    @26
    @2
    @124
    @66
    ad3antrrr
    lenltd
    mpbid
    syldan
    pm2.21d
    ralrimiva
    @120
    @84
    @122
    vw
    @54
    @120
    @80
    @121
    @83
    @120
    @45
    cB
    @44
    clt
    @45
    cB
    elsni
    breq1d
    imbi1d
    ralbidv
    syl5ibrcom
    ralrimiv
    @85
    vz
    @5
    @53
    ralunb
    sylanbrc
    @29
    @92
    @54
    @19
    wss
    #
    @70
    @86
    wb
    #
    @95
    @29
    @5
    @53
    @19
    @97
    @29
    cB
    @19
    @67
    snssd
    unssd
    @98
    @99
    @92
    @128
    wa
    @129
    @102
    erdszelem.o
    vz
    vw
    @54
    @19
    cr
    clt
    cO
    cF
    soisores
    mpanl12
    syl2anc
    mpbird
    @29
    @71
    @53
    @54
    wss
    #
    @53
    @5
    ssun2
    @29
    @77
    @71
    @130
    wb
    @78
    cB
    @54
    @38
    snssg
    syl
    mpbiri
    vy
    cB
    @39
    cF
    cO
    @54
    @50
    erdszelem1
    syl3anbrc
    @15
    @54
    chash
    cdm
    #
    wcel
    @68
    @69
    wi
    @18
    @54
    cvv
    @131
    @5
    @53
    vf
    vex
    cB
    snex
    unex
    cvv
    @17
    chash
    hashf
    fdmi
    eleqtrri
    @39
    @54
    chash
    funfvima
    mp2an
    syl
    eqeltrrd
    #
    @40
    @36
    ne0i
    syl
    @29
    @42
    @48
    @46
    @52
    @48
    @49
    @51
    simpli
    vz
    vw
    @40
    fimaxre2
    sylancl
    @132
    vz
    vw
    @40
    @36
    suprub
    syl31anc
    wph
    @4
    @41
    wceq
    #
    @26
    @2
    wph
    @63
    @133
    erdszelem.b
    wph
    vx
    vy
    cB
    cF
    cK
    cN
    cO
    erdsze.n
    erdsze.f
    erdszelem.k
    erdszelem3
    syl
    ad2antrr
    breqtrrd
    @29
    @31
    @4
    cn0
    wcel
    @35
    @37
    wb
    @34
    @29
    @4
    wph
    @4
    cn
    wcel
    @26
    @2
    wph
    @19
    cn
    cB
    cK
    wph
    vx
    vy
    cF
    cK
    cN
    cO
    erdsze.n
    erdsze.f
    erdszelem.k
    erdszelem.o
    erdszelem6
    erdszelem.b
    ffvelrnd
    ad2antrr
    nnnn0d
    @6
    @4
    nn0ltp1le
    syl2anc
    mpbird
    ltned
    ex
    @7
    @28
    @13
    @2
    @6
    @3
    @4
    neeq1
    imbi2d
    syl5ibcom
    sylan2b
    rexlimdva
    mpd
    necon2bd
end
