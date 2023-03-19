include "cn.mm"
include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "clt.mm"
include "wiso.mm"
include "chash.mm"
include "c1.mm"
include "cmin.mm"
include "c2.mm"
include "cuz.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "2z.mm"
include "a1i.mm"
include "c0.mm"
include "wne.mm"
include "cpr.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "crn.mm"
include "wrex.mm"
include "cicc.mm"
include "crab.mm"
include "cun.mm"
include "cr.mm"
include "prid1g.mm"
include "elun1.mm"
include "3syl.mm"
include "syl6eleqr.mm"
include "ne0i.mm"
include "syl.mm"
include "cfn.mm"
include "wb.mm"
include "prfi.mm"
include "w3a.mm"
include "wa.mm"
include "cabs.mm"
include "ccom.mm"
include "cxp.mm"
include "cid.mm"
include "cdif.mm"
include "cres.mm"
include "cinf.mm"
include "cioo.mm"
include "ctg.mm"
include "crest.mm"
include "fourierdlem11.mm"
include "simp1d.mm"
include "simp2d.mm"
include "simp3d.mm"
include "wf.mm"
include "wss.mm"
include "fourierdlem15.mm"
include "frn.mm"
include "wfn.mm"
include "cmap.mm"
include "wceq.mm"
include "cfzo.mm"
include "wral.mm"
include "fourierdlem2.mm"
include "mpbid.mm"
include "simpld.mm"
include "elmapi.mm"
include "ffn.mm"
include "fzfid.mm"
include "fnfi.mm"
include "syl2anc.mm"
include "rnfi.mm"
include "simprd.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "eluzfz1.mm"
include "fnfvelrn.mm"
include "eqeltrrd.mm"
include "eluzfz2.mm"
include "eqid.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "rexbidv.mm"
include "cbvrabv.mm"
include "oveq2d.mm"
include "anbi1d.mm"
include "anbi2d.mm"
include "cbvrex2v.mm"
include "anbi2i.mm"
include "fourierdlem42.mm"
include "unfi.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "hashnncl.mm"
include "mpbird.mm"
include "nnzd.mm"
include "ltned.mm"
include "hashprg.mm"
include "eqcomd.mm"
include "ssun1.mm"
include "syl6sseqr.mm"
include "hashssle.mm"
include "eqbrtrd.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "uz2m1nn.mm"
include "wf1o.mm"
include "prssg.mm"
include "mpbi2and.mm"
include "ssrab2.mm"
include "iccssred.mm"
include "syl5ss.mm"
include "unssd.mm"
include "syl5eqss.mm"
include "fourierdlem36.mm"
include "df-isom.mm"
include "sylib.mm"
include "f1of.mm"
include "fssd.mm"
include "cvv.mm"
include "reex.mm"
include "ovex.mm"
include "elmapg.mm"
include "wfo.mm"
include "wf1.mm"
include "df-f1o.mm"
include "dffo3.mm"
include "eqeq1.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "rspcv.mm"
include "sylc.mm"
include "fveq2.mm"
include "adantl.mm"
include "simplr.mm"
include "eqtrd.mm"
include "ad2antrr.mm"
include "eqeltrd.mm"
include "eqled.mm"
include "3adantl2.mm"
include "wn.mm"
include "cxr.mm"
include "rexrd.mm"
include "ltled.mm"
include "lbicc2.mm"
include "syl3anc.mm"
include "ubicc2.mm"
include "nnm1nn0.mm"
include "ffvelrnd.mm"
include "sseldd.mm"
include "adantr.mm"
include "3ad2antl1.mm"
include "elfzelz.mm"
include "zred.mm"
include "elfzle1.mm"
include "neqne.mm"
include "ne0gt0d.mm"
include "3ad2antl2.mm"
include "simpl1.mm"
include "simpl2.mm"
include "breq1.mm"
include "breq1d.mm"
include "bibi12d.mm"
include "ralbidv.mm"
include "r19.21bi.mm"
include "simpl3.mm"
include "breqtrd.mm"
include "pm2.61dan.mm"
include "rexlimdv3a.mm"
include "mpd.mm"
include "elicc2.mm"
include "letri3d.mm"
include "mpbir2and.mm"
include "prid2g.mm"
include "biimpri.mm"
include "3ad2ant3.mm"
include "ffvelrnda.mm"
include "elfzel2.mm"
include "elfzle2.mm"
include "lensymd.mm"
include "mtbid.mm"
include "nltled.mm"
include "3adant3.mm"
include "elfzoelz.mm"
include "ltp1d.mm"
include "wi.mm"
include "elfzofz.mm"
include "fzofzp1.mm"
include "breq2.mm"
include "breq2d.mm"
include "rspc2v.mm"
include "ralrimiva.mm"
include "jca31.mm"

theorem fourierdlem54
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let vk: setvar k
  let vm: setvar m
  let cH: class H
  let cM: class M
  let cN: class N
  let cO: class O
  let vp: setvar p
  let vw: setvar w
  let vh: setvar h
  let vy: setvar y
  let vz: setvar z
  let vj: setvar j
  let vl: setvar l
  assume fourierdlem54.t: |- T = ( B - A )
  assume fourierdlem54.p: |- P = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = A /\ ( p ` m ) = B ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem54.m: |- ( ph -> M e. NN )
  assume fourierdlem54.q: |- ( ph -> Q e. ( P ` M ) )
  assume fourierdlem54.c: |- ( ph -> C e. RR )
  assume fourierdlem54.d: |- ( ph -> D e. RR )
  assume fourierdlem54.cd: |- ( ph -> C < D )
  assume fourierdlem54.o: |- O = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = C /\ ( p ` m ) = D ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem54.h: |- H = ( { C , D } u. { x e. ( C [,] D ) | E. k e. ZZ ( x + ( k x. T ) ) e. ran Q } )
  assume fourierdlem54.n: |- N = ( ( # ` H ) - 1 )
  assume fourierdlem54.s: |- S = ( iota f f Isom < , < ( ( 0 ... N ) , H ) )

  disjoint A i
  disjoint A m
  disjoint A p
  disjoint i m
  disjoint i p
  disjoint m p
  disjoint B i
  disjoint B m
  disjoint B p
  disjoint C m
  disjoint C p
  disjoint C x
  disjoint D m
  disjoint D p
  disjoint D x
  disjoint H f
  disjoint H x
  disjoint M i
  disjoint M m
  disjoint M p
  disjoint N f
  disjoint N i
  disjoint N m
  disjoint N p
  disjoint N x
  disjoint i x
  disjoint Q i
  disjoint Q k
  disjoint i k
  disjoint Q p
  disjoint Q x
  disjoint k x
  disjoint S f
  disjoint S i
  disjoint S p
  disjoint S x
  disjoint T i
  disjoint T k
  disjoint T x
  disjoint f ph
  disjoint i ph
  disjoint k ph
  disjoint k x
  disjoint A w
  disjoint B w
  disjoint C h
  disjoint C y
  disjoint h y
  disjoint C w
  disjoint C z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint D h
  disjoint D y
  disjoint D w
  disjoint D z
  disjoint H h
  disjoint H y
  disjoint N h
  disjoint N y
  disjoint i y
  disjoint Q j
  disjoint Q l
  disjoint Q y
  disjoint Q z
  disjoint i j
  disjoint i l
  disjoint i z
  disjoint j k
  disjoint j l
  disjoint j y
  disjoint j z
  disjoint k l
  disjoint k y
  disjoint k z
  disjoint l y
  disjoint l z
  disjoint Q w
  disjoint j w
  disjoint k w
  disjoint S h
  disjoint S y
  disjoint T j
  disjoint T l
  disjoint T y
  disjoint T z
  disjoint T w
  disjoint j ph
  disjoint ph y
  disjoint ph z
  disjoint ph w
  assert |- ( ph -> ( ( N e. NN /\ S e. ( O ` N ) ) /\ S Isom < , < ( ( 0 ... N ) , H ) ) )

  proof
    wph
    cN
    cn
    wcel
    #
    cS
    cN
    cO
    cfv
    wcel
    #
    cc0
    cN
    cfz
    co
    #
    cH
    clt
    clt
    cS
    wiso
    #
    wph
    cN
    cH
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cn
    fourierdlem54.n
    wph
    @4
    c2
    cuz
    cfv
    wcel
    #
    @5
    cn
    wcel
    wph
    c2
    cz
    wcel
    #
    @4
    cz
    wcel
    c2
    @4
    cle
    wbr
    @6
    @7
    wph
    2z
    a1i
    wph
    @4
    wph
    @4
    cn
    wcel
    #
    cH
    c0
    wne
    #
    wph
    cC
    cH
    wcel
    #
    @9
    wph
    cC
    cC
    cD
    cpr
    #
    vx
    cv
    #
    vk
    cv
    #
    cT
    cmul
    co
    #
    caddc
    co
    #
    cQ
    crn
    #
    wcel
    #
    vk
    cz
    wrex
    #
    vx
    cC
    cD
    cicc
    co
    #
    crab
    #
    cun
    #
    cH
    wph
    cC
    cr
    wcel
    #
    cC
    @11
    wcel
    cC
    @21
    wcel
    fourierdlem54.c
    cC
    cD
    cr
    prid1g
    cC
    @11
    @20
    elun1
    3syl
    fourierdlem54.h
    syl6eleqr
    #
    cH
    cC
    ne0i
    syl
    wph
    cH
    cfn
    wcel
    #
    @8
    @9
    wb
    wph
    cH
    @21
    cfn
    fourierdlem54.h
    wph
    @11
    cfn
    wcel
    @20
    cfn
    wcel
    @21
    cfn
    wcel
    cC
    cD
    prfi
    wph
    wph
    vy
    cv
    #
    cr
    wcel
    #
    vz
    cv
    #
    cr
    wcel
    @25
    @27
    clt
    wbr
    w3a
    wa
    #
    @25
    vi
    cv
    #
    cT
    cmul
    co
    #
    caddc
    co
    #
    @16
    wcel
    #
    @27
    vl
    cv
    #
    cT
    cmul
    co
    #
    caddc
    co
    #
    @16
    wcel
    #
    wa
    #
    vl
    cz
    wrex
    vi
    cz
    wrex
    #
    wa
    vw
    @16
    cA
    cB
    cabs
    cmin
    ccom
    #
    @39
    @16
    @16
    cxp
    cid
    cdif
    #
    cres
    crn
    #
    cT
    vj
    vk
    @41
    cr
    clt
    cinf
    #
    @20
    @40
    cioo
    crn
    ctg
    cfv
    #
    @43
    @19
    crest
    co
    #
    cC
    cD
    vy
    vz
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    clt
    wbr
    #
    wph
    cA
    cB
    cP
    cQ
    vi
    vm
    cM
    vp
    fourierdlem54.p
    fourierdlem54.m
    fourierdlem54.q
    fourierdlem11
    #
    simp1d
    wph
    @45
    @46
    @47
    @48
    simp2d
    wph
    @45
    @46
    @47
    @48
    simp3d
    fourierdlem54.t
    wph
    cc0
    cM
    cfz
    co
    #
    cA
    cB
    cicc
    co
    #
    cQ
    wf
    @16
    @50
    wss
    wph
    cA
    cB
    cP
    cQ
    vi
    vm
    cM
    vp
    fourierdlem54.p
    fourierdlem54.m
    fourierdlem54.q
    fourierdlem15
    @49
    @50
    cQ
    frn
    syl
    wph
    cQ
    cfn
    wcel
    #
    @16
    cfn
    wcel
    wph
    cQ
    @49
    wfn
    #
    @49
    cfn
    wcel
    @51
    wph
    cQ
    cr
    @49
    cmap
    co
    wcel
    #
    @49
    cr
    cQ
    wf
    @52
    wph
    @53
    cc0
    cQ
    cfv
    #
    cA
    wceq
    #
    cM
    cQ
    cfv
    #
    cB
    wceq
    #
    wa
    #
    @29
    cQ
    cfv
    @29
    c1
    caddc
    co
    #
    cQ
    cfv
    clt
    wbr
    vi
    cc0
    cM
    cfzo
    co
    wral
    #
    wa
    #
    wph
    cQ
    cM
    cP
    cfv
    wcel
    #
    @53
    @61
    wa
    #
    fourierdlem54.q
    wph
    cM
    cn
    wcel
    @62
    @63
    wb
    fourierdlem54.m
    cA
    cB
    cP
    cQ
    vi
    vm
    cM
    vp
    fourierdlem54.p
    fourierdlem2
    syl
    mpbid
    #
    simpld
    cQ
    cr
    @49
    elmapi
    @49
    cr
    cQ
    ffn
    3syl
    #
    wph
    cc0
    cM
    fzfid
    @49
    cQ
    fnfi
    syl2anc
    cQ
    rnfi
    syl
    wph
    @54
    cA
    @16
    wph
    @55
    @57
    wph
    @58
    @60
    wph
    @53
    @61
    @64
    simprd
    simpld
    #
    simpld
    wph
    @52
    cc0
    @49
    wcel
    #
    @54
    @16
    wcel
    @65
    wph
    cM
    cc0
    cuz
    cfv
    #
    wcel
    #
    @67
    wph
    cM
    cn0
    @68
    wph
    cM
    fourierdlem54.m
    nnnn0d
    nn0uz
    syl6eleq
    #
    cc0
    cM
    eluzfz1
    syl
    @49
    cc0
    cQ
    fnfvelrn
    syl2anc
    eqeltrrd
    wph
    @56
    cB
    @16
    wph
    @55
    @57
    @66
    simprd
    wph
    @52
    cM
    @49
    wcel
    #
    @56
    @16
    wcel
    @65
    wph
    @69
    @71
    @70
    cc0
    cM
    eluzfz2
    syl
    @49
    cM
    cQ
    fnfvelrn
    syl2anc
    eqeltrrd
    @39
    eqid
    @40
    eqid
    @41
    eqid
    @42
    eqid
    fourierdlem54.c
    fourierdlem54.d
    @43
    eqid
    @44
    eqid
    @18
    vw
    cv
    #
    @14
    caddc
    co
    #
    @16
    wcel
    #
    vk
    cz
    wrex
    vx
    vw
    @19
    @12
    @72
    wceq
    #
    @17
    @74
    vk
    cz
    @75
    @15
    @73
    @16
    @12
    @72
    @14
    caddc
    oveq1
    eleq1d
    rexbidv
    cbvrabv
    @38
    @25
    vj
    cv
    #
    cT
    cmul
    co
    #
    caddc
    co
    #
    @16
    wcel
    #
    @27
    @14
    caddc
    co
    #
    @16
    wcel
    #
    wa
    #
    vk
    cz
    wrex
    vj
    cz
    wrex
    @28
    @37
    @82
    @79
    @36
    wa
    vi
    vl
    vj
    vk
    cz
    cz
    @29
    @76
    wceq
    #
    @32
    @79
    @36
    @83
    @31
    @78
    @16
    @83
    @30
    @77
    @25
    caddc
    @29
    @76
    cT
    cmul
    oveq1
    oveq2d
    eleq1d
    anbi1d
    @33
    @13
    wceq
    #
    @36
    @81
    @79
    @84
    @35
    @80
    @16
    @84
    @34
    @14
    @27
    caddc
    @33
    @13
    cT
    cmul
    oveq1
    oveq2d
    eleq1d
    anbi2d
    cbvrex2v
    anbi2i
    fourierdlem42
    @11
    @20
    unfi
    sylancr
    syl5eqel
    #
    cH
    hashnncl
    syl
    mpbird
    #
    nnzd
    wph
    c2
    @11
    chash
    cfv
    #
    @4
    cle
    wph
    @87
    c2
    wph
    cC
    cD
    wne
    #
    @87
    c2
    wceq
    #
    wph
    cC
    cD
    fourierdlem54.c
    fourierdlem54.cd
    ltned
    wph
    @22
    cD
    cr
    wcel
    #
    @88
    @89
    wb
    fourierdlem54.c
    fourierdlem54.d
    cC
    cD
    cr
    cr
    hashprg
    syl2anc
    mpbid
    eqcomd
    wph
    @24
    @11
    cH
    wss
    @87
    @4
    cle
    wbr
    @85
    wph
    @11
    @21
    cH
    @11
    @21
    wss
    wph
    @11
    @20
    ssun1
    a1i
    fourierdlem54.h
    syl6sseqr
    cH
    @11
    hashssle
    syl2anc
    eqbrtrd
    c2
    @4
    eluz2
    syl3anbrc
    @4
    uz2m1nn
    syl
    syl5eqel
    #
    wph
    @1
    cS
    cr
    @2
    cmap
    co
    wcel
    #
    cc0
    cS
    cfv
    #
    cC
    wceq
    #
    cN
    cS
    cfv
    #
    cD
    wceq
    #
    wa
    @29
    cS
    cfv
    #
    @59
    cS
    cfv
    #
    clt
    wbr
    #
    vi
    cc0
    cN
    cfzo
    co
    #
    wral
    #
    wa
    #
    wph
    @92
    @2
    cr
    cS
    wf
    #
    wph
    @2
    cH
    cr
    cS
    wph
    @2
    cH
    cS
    wf1o
    #
    @2
    cH
    cS
    wf
    #
    wph
    @104
    @12
    @25
    clt
    wbr
    #
    @12
    cS
    cfv
    #
    @25
    cS
    cfv
    #
    clt
    wbr
    #
    wb
    #
    vy
    @2
    wral
    #
    vx
    @2
    wral
    #
    wph
    @3
    @104
    @112
    wa
    wph
    cH
    vf
    cS
    cN
    @85
    wph
    cH
    @21
    cr
    fourierdlem54.h
    wph
    @11
    @20
    cr
    wph
    @22
    @90
    @11
    cr
    wss
    #
    fourierdlem54.c
    fourierdlem54.d
    wph
    @22
    @90
    @22
    @90
    wa
    @113
    wb
    fourierdlem54.c
    fourierdlem54.d
    cC
    cD
    cr
    cr
    cr
    prssg
    syl2anc
    mpbi2and
    wph
    @20
    @19
    cr
    @18
    vx
    @19
    ssrab2
    #
    wph
    cC
    cD
    fourierdlem54.c
    fourierdlem54.d
    iccssred
    #
    syl5ss
    unssd
    syl5eqss
    #
    fourierdlem54.s
    fourierdlem54.n
    fourierdlem36
    #
    vx
    vy
    @2
    cH
    clt
    clt
    cS
    df-isom
    sylib
    #
    simpld
    #
    @2
    cH
    cS
    f1of
    syl
    #
    @116
    fssd
    #
    wph
    cr
    cvv
    wcel
    @2
    cvv
    wcel
    #
    @92
    @103
    wb
    reex
    @122
    wph
    cc0
    cN
    cfz
    ovex
    a1i
    cr
    @2
    cS
    cvv
    cvv
    elmapg
    sylancr
    mpbird
    wph
    @94
    @96
    @101
    wph
    @94
    @93
    cC
    cle
    wbr
    #
    cC
    @93
    cle
    wbr
    #
    wph
    @108
    cC
    wceq
    #
    vy
    @2
    wrex
    #
    @123
    wph
    @10
    vh
    cv
    #
    @108
    wceq
    #
    vy
    @2
    wrex
    #
    vh
    cH
    wral
    #
    @126
    @23
    wph
    @105
    @130
    wph
    @2
    cH
    cS
    wfo
    #
    @105
    @130
    wa
    wph
    @2
    cH
    cS
    wf1
    #
    @131
    wph
    @104
    @132
    @131
    wa
    @119
    @2
    cH
    cS
    df-f1o
    sylib
    simprd
    vy
    vh
    @2
    cH
    cS
    dffo3
    sylib
    simprd
    #
    @129
    @126
    vh
    cC
    cH
    @127
    cC
    wceq
    #
    @128
    @125
    vy
    @2
    @134
    @128
    cC
    @108
    wceq
    @125
    @127
    cC
    @108
    eqeq1
    cC
    @108
    eqcom
    syl6bb
    rexbidv
    rspcv
    sylc
    wph
    @125
    @123
    vy
    @2
    wph
    @25
    @2
    wcel
    #
    @125
    w3a
    #
    @25
    cc0
    wceq
    #
    @123
    wph
    @125
    @137
    @123
    @135
    wph
    @125
    wa
    #
    @137
    wa
    #
    @93
    cC
    @139
    @93
    cC
    cr
    @139
    @93
    @108
    cC
    @137
    @93
    @108
    wceq
    @138
    @137
    @108
    @93
    @25
    cc0
    cS
    fveq2
    eqcomd
    adantl
    wph
    @125
    @137
    simplr
    eqtrd
    #
    wph
    @22
    @125
    @137
    fourierdlem54.c
    ad2antrr
    eqeltrd
    @140
    eqled
    3adantl2
    @136
    @137
    wn
    #
    wa
    #
    @93
    cC
    wph
    @135
    @141
    @93
    cr
    wcel
    #
    @125
    wph
    @143
    @141
    wph
    @19
    cr
    @93
    @115
    wph
    cH
    @19
    @93
    wph
    cH
    @21
    @19
    fourierdlem54.h
    wph
    @11
    @20
    @19
    wph
    cC
    @19
    wcel
    #
    cD
    @19
    wcel
    #
    @11
    @19
    wss
    #
    wph
    cC
    cxr
    wcel
    #
    cD
    cxr
    wcel
    #
    cC
    cD
    cle
    wbr
    #
    @144
    wph
    cC
    fourierdlem54.c
    rexrd
    #
    wph
    cD
    fourierdlem54.d
    rexrd
    #
    wph
    cC
    cD
    fourierdlem54.c
    fourierdlem54.d
    fourierdlem54.cd
    ltled
    #
    cC
    cD
    lbicc2
    syl3anc
    #
    wph
    @147
    @148
    @149
    @145
    @150
    @151
    @152
    cC
    cD
    ubicc2
    syl3anc
    #
    wph
    @144
    @145
    @144
    @145
    wa
    @146
    wb
    @153
    @154
    cC
    cD
    @19
    @19
    @19
    prssg
    syl2anc
    mpbi2and
    @20
    @19
    wss
    wph
    @114
    a1i
    unssd
    syl5eqss
    #
    wph
    @2
    cH
    cc0
    cS
    @120
    wph
    cN
    @68
    wcel
    #
    cc0
    @2
    wcel
    #
    wph
    cN
    cn0
    @68
    wph
    cN
    @5
    cn0
    fourierdlem54.n
    wph
    @8
    @5
    cn0
    wcel
    @86
    @4
    nnm1nn0
    syl
    syl5eqel
    nn0uz
    syl6eleq
    #
    cc0
    cN
    eluzfz1
    syl
    #
    ffvelrnd
    sseldd
    #
    sseldd
    #
    adantr
    3ad2antl1
    wph
    @135
    @141
    @22
    @125
    wph
    @22
    @141
    fourierdlem54.c
    adantr
    3ad2antl1
    @142
    @93
    @108
    cC
    clt
    @142
    cc0
    @25
    clt
    wbr
    #
    @93
    @108
    clt
    wbr
    #
    @135
    wph
    @141
    @162
    @125
    @135
    @141
    wa
    @25
    @135
    @26
    @141
    @135
    @25
    @25
    cc0
    cN
    elfzelz
    zred
    #
    adantr
    @135
    cc0
    @25
    cle
    wbr
    @141
    @25
    cc0
    cN
    elfzle1
    adantr
    @141
    @25
    cc0
    wne
    @135
    @25
    cc0
    neqne
    adantl
    ne0gt0d
    3ad2antl2
    @142
    wph
    @135
    @162
    @163
    wb
    #
    wph
    @135
    @125
    @141
    simpl1
    wph
    @135
    @125
    @141
    simpl2
    wph
    @165
    vy
    @2
    wph
    @157
    @112
    @165
    vy
    @2
    wral
    #
    @159
    wph
    @104
    @112
    @118
    simprd
    #
    @111
    @166
    vx
    cc0
    @2
    @12
    cc0
    wceq
    #
    @110
    @165
    vy
    @2
    @168
    @106
    @162
    @109
    @163
    @12
    cc0
    @25
    clt
    breq1
    @168
    @107
    @93
    @108
    clt
    @12
    cc0
    cS
    fveq2
    breq1d
    bibi12d
    ralbidv
    rspcv
    sylc
    r19.21bi
    syl2anc
    mpbid
    wph
    @135
    @125
    @141
    simpl3
    breqtrd
    ltled
    pm2.61dan
    rexlimdv3a
    mpd
    wph
    @143
    @124
    @93
    cD
    cle
    wbr
    #
    wph
    @93
    @19
    wcel
    #
    @143
    @124
    @169
    w3a
    #
    @160
    wph
    @22
    @90
    @170
    @171
    wb
    fourierdlem54.c
    fourierdlem54.d
    cC
    cD
    @93
    elicc2
    syl2anc
    mpbid
    simp2d
    wph
    @93
    cC
    @161
    fourierdlem54.c
    letri3d
    mpbir2and
    wph
    @96
    @95
    cD
    cle
    wbr
    #
    cD
    @95
    cle
    wbr
    #
    wph
    @95
    cr
    wcel
    #
    cC
    @95
    cle
    wbr
    #
    @172
    wph
    @95
    @19
    wcel
    #
    @174
    @175
    @172
    w3a
    #
    wph
    cH
    @19
    @95
    @155
    wph
    @2
    cH
    cN
    cS
    @120
    wph
    @156
    cN
    @2
    wcel
    #
    @158
    cc0
    cN
    eluzfz2
    syl
    #
    ffvelrnd
    sseldd
    #
    wph
    @22
    @90
    @176
    @177
    wb
    fourierdlem54.c
    fourierdlem54.d
    cC
    cD
    @95
    elicc2
    syl2anc
    mpbid
    simp3d
    wph
    @108
    cD
    wceq
    #
    vy
    @2
    wrex
    #
    @173
    wph
    cD
    cH
    wcel
    @130
    @182
    wph
    cD
    @21
    cH
    wph
    @90
    cD
    @11
    wcel
    cD
    @21
    wcel
    fourierdlem54.d
    cC
    cD
    cr
    prid2g
    cD
    @11
    @20
    elun1
    3syl
    fourierdlem54.h
    syl6eleqr
    @133
    @129
    @182
    vh
    cD
    cH
    @127
    cD
    wceq
    #
    @128
    @181
    vy
    @2
    @183
    @128
    cD
    @108
    wceq
    #
    @181
    @127
    cD
    @108
    eqeq1
    cD
    @108
    eqcom
    #
    syl6bb
    rexbidv
    rspcv
    sylc
    wph
    @181
    @173
    vy
    @2
    wph
    @135
    @181
    w3a
    cD
    @108
    @95
    cle
    @181
    wph
    @184
    @135
    @184
    @181
    @185
    biimpri
    3ad2ant3
    wph
    @135
    @108
    @95
    cle
    wbr
    @181
    wph
    @135
    wa
    #
    @108
    @95
    wph
    @2
    cr
    @25
    cS
    @121
    ffvelrnda
    wph
    @174
    @135
    wph
    @19
    cr
    @95
    @115
    @180
    sseldd
    #
    adantr
    @186
    cN
    @25
    clt
    wbr
    #
    @95
    @108
    clt
    wbr
    #
    @186
    @25
    cN
    @135
    @26
    wph
    @164
    adantl
    @135
    cN
    cr
    wcel
    wph
    @135
    cN
    @25
    cc0
    cN
    elfzel2
    zred
    adantl
    @135
    @25
    cN
    cle
    wbr
    wph
    @25
    cc0
    cN
    elfzle2
    adantl
    lensymd
    wph
    @188
    @189
    wb
    #
    vy
    @2
    wph
    @178
    @112
    @190
    vy
    @2
    wral
    #
    @179
    @167
    @111
    @191
    vx
    cN
    @2
    @12
    cN
    wceq
    #
    @110
    @190
    vy
    @2
    @192
    @106
    @188
    @109
    @189
    @12
    cN
    @25
    clt
    breq1
    @192
    @107
    @95
    @108
    clt
    @12
    cN
    cS
    fveq2
    breq1d
    bibi12d
    ralbidv
    rspcv
    sylc
    r19.21bi
    mtbid
    nltled
    3adant3
    eqbrtrd
    rexlimdv3a
    mpd
    wph
    @95
    cD
    @187
    fourierdlem54.d
    letri3d
    mpbir2and
    wph
    @99
    vi
    @100
    wph
    @29
    @100
    wcel
    #
    wa
    #
    @29
    @59
    clt
    wbr
    #
    @99
    @193
    @195
    wph
    @193
    @29
    @193
    @29
    @29
    cc0
    cN
    elfzoelz
    zred
    ltp1d
    adantl
    @194
    @112
    @195
    @99
    wb
    #
    wph
    @112
    @193
    @167
    adantr
    @194
    @29
    @2
    wcel
    #
    @59
    @2
    wcel
    #
    @112
    @196
    wi
    @193
    @197
    wph
    @29
    cc0
    cN
    elfzofz
    adantl
    @193
    @198
    wph
    cc0
    cN
    @29
    fzofzp1
    adantl
    @110
    @196
    @29
    @25
    clt
    wbr
    #
    @97
    @108
    clt
    wbr
    #
    wb
    vx
    vy
    @29
    @59
    @2
    @2
    @12
    @29
    wceq
    #
    @106
    @199
    @109
    @200
    @12
    @29
    @25
    clt
    breq1
    @201
    @107
    @97
    @108
    clt
    @12
    @29
    cS
    fveq2
    breq1d
    bibi12d
    @25
    @59
    wceq
    #
    @199
    @195
    @200
    @99
    @25
    @59
    @29
    clt
    breq2
    @202
    @108
    @98
    @97
    clt
    @25
    @59
    cS
    fveq2
    breq2d
    bibi12d
    rspc2v
    syl2anc
    mpd
    mpbid
    ralrimiva
    jca31
    wph
    @0
    @1
    @92
    @102
    wa
    wb
    @91
    cC
    cD
    cO
    cS
    vi
    vm
    cN
    vp
    fourierdlem54.o
    fourierdlem2
    syl
    mpbir2and
    @117
    jca31
end
