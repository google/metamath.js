include "culm.mm"
include "cfv.mm"
include "wbr.mm"
include "cc0.mm"
include "clt.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "wss.mm"
include "cabs.mm"
include "ccnv.mm"
include "cicc.mm"
include "co.mm"
include "cima.mm"
include "adantr.mm"
include "cxr.mm"
include "wcel.mm"
include "wb.mm"
include "0xr.mm"
include "rexrd.mm"
include "icc0.mm"
include "sylancr.mm"
include "biimpar.mm"
include "imaeq2d.mm"
include "ima0.mm"
include "syl6eq.mm"
include "sseqtrd.mm"
include "ss0.mm"
include "syl.mm"
include "cn0.mm"
include "nn0uz.mm"
include "0zd.mm"
include "cv.mm"
include "caddc.mm"
include "cseq.mm"
include "cmpt.mm"
include "cc.mm"
include "cmap.mm"
include "wf.mm"
include "cdm.mm"
include "cnvimass.mm"
include "cr.mm"
include "absf.mm"
include "fdmi.mm"
include "sseqtri.mm"
include "syl6ss.mm"
include "sselda.mm"
include "psergf.mm"
include "ffvelrnda.mm"
include "serf.mm"
include "an32s.mm"
include "eqid.mm"
include "fmptd.mm"
include "cvv.mm"
include "cnex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "elmapg.mm"
include "mpbird.mm"
include "csu.mm"
include "eqidd.mm"
include "cle.mm"
include "w3a.mm"
include "wfn.mm"
include "ffn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "sylib.mm"
include "simprd.mm"
include "0re.mm"
include "elicc2.mm"
include "mpbid.mm"
include "simp1d.mm"
include "cpnf.mm"
include "iccssxr.mm"
include "radcnvcl.mm"
include "sseldi.mm"
include "simp3d.mm"
include "xrlelttrd.mm"
include "radcnvlt2.mm"
include "isumcl.mm"
include "ulm0.mm"
include "syldan.mm"
include "cof.mm"
include "cuz.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "cfz.mm"
include "elfznn0.mm"
include "adantl.mm"
include "ad2antrr.mm"
include "mptexg.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "cbvmptv.mm"
include "mpteq2dv.mm"
include "syl5eq.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "seqof.mm"
include "eqcomd.mm"
include "mpteq2dva.mm"
include "cz.mm"
include "0z.mm"
include "seqfn.mm"
include "ax-mp.mm"
include "fneq2i.mm"
include "mpbir.mm"
include "dffn5.mm"
include "mpbi.mm"
include "3eqtr4g.mm"
include "ccom.mm"
include "fex.mm"
include "mp2an.mm"
include "fvex.mm"
include "coex.mm"
include "a1i.mm"
include "recnd.mm"
include "fco.mm"
include "cexp.mm"
include "cmul.mm"
include "simprr.mm"
include "sseldd.mm"
include "simprl.mm"
include "expcld.mm"
include "abscld.mm"
include "ffvelrnd.mm"
include "absge0d.mm"
include "wral.mm"
include "ralrimiva.mm"
include "breq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "leexp1a.mm"
include "syl32anc.mm"
include "absexpd.mm"
include "absid.mm"
include "sylan.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "3brtr4d.mm"
include "lemul2ad.mm"
include "absmuld.mm"
include "fvmpt.mm"
include "ad2antll.mm"
include "pserval2.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "fvco3.mm"
include "cli.mm"
include "eqbrtrd.mm"
include "id.mm"
include "oveq12d.mm"
include "radcnvlt1.mm"
include "mtest.mm"
include "eqeltrd.mm"
include "wex.mm"
include "eldmg.mm"
include "ibi.mm"
include "ulmcl.mm"
include "feqmptd.mm"
include "adantlr.mm"
include "seqex.mm"
include "ad3antrrr.mm"
include "fvmpt2.mm"
include "simplr.mm"
include "ulmclm.mm"
include "isumclim.mm"
include "eqtr4d.mm"
include "breqtrd.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5.mm"
include "imp.mm"
include "0red.mm"
include "ltlecasei.mm"

theorem pserulm
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let vr: setvar r
  let va: setvar a
  let vk: setvar k
  let vm: setvar m
  let vs: setvar s
  let vw: setvar w
  let vz: setvar z
  let vf: setvar f
  let vu: setvar u
  let vv: setvar v
  let cB: class B
  assume pserf.g: |- G = ( x e. CC |-> ( n e. NN0 |-> ( ( A ` n ) x. ( x ^ n ) ) ) )
  assume pserf.f: |- F = ( y e. S |-> sum_ j e. NN0 ( ( G ` y ) ` j ) )
  assume pserf.a: |- ( ph -> A : NN0 --> CC )
  assume pserf.r: |- R = sup ( { r e. RR | seq 0 ( + , ( G ` r ) ) e. dom ~~> } , RR* , < )
  assume pserulm.h: |- H = ( i e. NN0 |-> ( y e. S |-> ( seq 0 ( + , ( G ` y ) ) ` i ) ) )
  assume pserulm.m: |- ( ph -> M e. RR )
  assume pserulm.l: |- ( ph -> M < R )
  assume pserulm.y: |- ( ph -> S C_ ( `' abs " ( 0 [,] M ) ) )

  disjoint j n
  disjoint j r
  disjoint j x
  disjoint j y
  disjoint A j
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint r x
  disjoint r y
  disjoint A r
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint i j
  disjoint i y
  disjoint H i
  disjoint H j
  disjoint H y
  disjoint M i
  disjoint M j
  disjoint M y
  disjoint i x
  disjoint i r
  disjoint G i
  disjoint G j
  disjoint G r
  disjoint G y
  disjoint S i
  disjoint S j
  disjoint S y
  disjoint i ph
  disjoint j ph
  disjoint ph y
  disjoint a j
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a r
  disjoint a s
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint j k
  disjoint j m
  disjoint j s
  disjoint j w
  disjoint j z
  disjoint k m
  disjoint k n
  disjoint k r
  disjoint k s
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint m n
  disjoint m r
  disjoint m s
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n s
  disjoint n w
  disjoint n z
  disjoint r s
  disjoint r w
  disjoint r z
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint f i
  disjoint f j
  disjoint f y
  disjoint H f
  disjoint i k
  disjoint i m
  disjoint i s
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i z
  disjoint j u
  disjoint j v
  disjoint k u
  disjoint k v
  disjoint M k
  disjoint m u
  disjoint m v
  disjoint M m
  disjoint s u
  disjoint s v
  disjoint M s
  disjoint u v
  disjoint u w
  disjoint u y
  disjoint u z
  disjoint M u
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint M v
  disjoint M w
  disjoint M z
  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint G k
  disjoint G m
  disjoint G s
  disjoint G w
  disjoint G z
  disjoint a f
  disjoint a i
  disjoint S a
  disjoint f k
  disjoint f m
  disjoint f w
  disjoint f z
  disjoint S f
  disjoint S k
  disjoint S m
  disjoint S w
  disjoint S z
  disjoint F a
  disjoint F f
  disjoint F z
  disjoint a ph
  disjoint f ph
  disjoint k ph
  disjoint m ph
  disjoint ph w
  disjoint ph z
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R z
  assert |- ( ph -> H ( ~~>u ` S ) F )

  proof
    wph
    cH
    cF
    cS
    culm
    cfv
    #
    wbr
    #
    cM
    cc0
    wph
    cM
    cc0
    clt
    wbr
    #
    cS
    c0
    wceq
    #
    @1
    wph
    @2
    wa
    #
    cS
    c0
    wss
    @3
    @4
    cS
    cabs
    ccnv
    #
    cc0
    cM
    cicc
    co
    #
    cima
    #
    c0
    wph
    cS
    @7
    wss
    @2
    pserulm.y
    adantr
    @4
    @7
    @5
    c0
    cima
    c0
    @4
    @6
    c0
    @5
    wph
    @6
    c0
    wceq
    #
    @2
    wph
    cc0
    cxr
    wcel
    cM
    cxr
    wcel
    #
    @8
    @2
    wb
    0xr
    wph
    cM
    pserulm.m
    rexrd
    #
    cc0
    cM
    icc0
    sylancr
    biimpar
    imaeq2d
    @5
    ima0
    syl6eq
    sseqtrd
    cS
    ss0
    syl
    wph
    cS
    cH
    cF
    cc0
    cn0
    nn0uz
    wph
    0zd
    wph
    vi
    cn0
    vy
    cS
    vi
    cv
    #
    caddc
    vy
    cv
    #
    cG
    cfv
    #
    cc0
    cseq
    #
    cfv
    #
    cmpt
    #
    cc
    cS
    cmap
    co
    #
    cH
    wph
    @11
    cn0
    wcel
    #
    wa
    #
    @16
    @17
    wcel
    #
    cS
    cc
    @16
    wf
    #
    @19
    vy
    cS
    @15
    cc
    @16
    wph
    @12
    cS
    wcel
    #
    @18
    @15
    cc
    wcel
    wph
    @22
    wa
    #
    cn0
    cc
    @11
    @14
    @23
    vj
    @13
    cc0
    cn0
    nn0uz
    @23
    0zd
    #
    @23
    cn0
    cc
    vj
    cv
    #
    @13
    @23
    vx
    cA
    vn
    cG
    @12
    pserf.g
    wph
    cn0
    cc
    cA
    wf
    #
    @22
    pserf.a
    adantr
    #
    wph
    cS
    cc
    @12
    wph
    cS
    @7
    cc
    pserulm.y
    @7
    cabs
    cdm
    cc
    cabs
    @6
    cnvimass
    cc
    cr
    cabs
    absf
    fdmi
    sseqtri
    syl6ss
    #
    sselda
    #
    psergf
    #
    ffvelrnda
    #
    serf
    ffvelrnda
    an32s
    @16
    eqid
    #
    fmptd
    @19
    cc
    cvv
    wcel
    #
    cS
    cvv
    wcel
    #
    @20
    @21
    wb
    cnex
    wph
    @34
    @18
    wph
    cS
    cc
    wss
    #
    @33
    @34
    @28
    cnex
    cS
    cc
    cvv
    ssexg
    sylancl
    #
    adantr
    #
    cc
    cS
    @16
    cvv
    cvv
    elmapg
    sylancr
    mpbird
    pserulm.h
    fmptd
    #
    wph
    vy
    cS
    cn0
    @25
    @13
    cfv
    #
    vj
    csu
    #
    cc
    cF
    @23
    @39
    vj
    @13
    cc0
    cn0
    nn0uz
    @24
    @23
    @25
    cn0
    wcel
    #
    wa
    @39
    eqidd
    @31
    @23
    vx
    cA
    cR
    vn
    cG
    @12
    vr
    pserf.g
    @27
    pserf.r
    @29
    @23
    @12
    cabs
    cfv
    #
    cM
    cR
    @23
    @42
    @23
    @42
    cr
    wcel
    #
    cc0
    @42
    cle
    wbr
    #
    @42
    cM
    cle
    wbr
    #
    @23
    @42
    @6
    wcel
    #
    @43
    @44
    @45
    w3a
    #
    @23
    @12
    cc
    wcel
    #
    @46
    @23
    @12
    @7
    wcel
    #
    @48
    @46
    wa
    #
    wph
    cS
    @7
    @12
    pserulm.y
    sselda
    cc
    cr
    cabs
    wf
    #
    cabs
    cc
    wfn
    @49
    @50
    wb
    absf
    cc
    cr
    cabs
    ffn
    cc
    @12
    @6
    cabs
    elpreima
    mp2b
    sylib
    simprd
    @23
    cc0
    cr
    wcel
    cM
    cr
    wcel
    #
    @46
    @47
    wb
    0re
    wph
    @52
    @22
    pserulm.m
    adantr
    cc0
    cM
    @42
    elicc2
    sylancr
    mpbid
    #
    simp1d
    rexrd
    wph
    @9
    @22
    @10
    adantr
    wph
    cR
    cxr
    wcel
    @22
    wph
    cc0
    cpnf
    cicc
    co
    cxr
    cR
    cc0
    cpnf
    iccssxr
    wph
    vx
    cA
    cR
    vn
    cG
    vr
    pserf.g
    pserf.a
    pserf.r
    radcnvcl
    sseldi
    adantr
    @23
    @43
    @44
    @45
    @53
    simp3d
    #
    wph
    cM
    cR
    clt
    wbr
    #
    @22
    pserulm.l
    adantr
    xrlelttrd
    radcnvlt2
    isumcl
    pserf.f
    fmptd
    ulm0
    syldan
    wph
    cc0
    cM
    cle
    wbr
    #
    cH
    @0
    cdm
    #
    wcel
    #
    @1
    wph
    @56
    wa
    #
    cH
    caddc
    cof
    #
    vm
    cn0
    vw
    cS
    vm
    cv
    #
    vw
    cv
    #
    cG
    cfv
    #
    cfv
    #
    cmpt
    #
    cmpt
    #
    cc0
    cseq
    #
    @57
    wph
    cH
    @67
    wceq
    @56
    wph
    vi
    cn0
    @16
    cmpt
    vi
    cn0
    @11
    @67
    cfv
    #
    cmpt
    #
    cH
    @67
    wph
    vi
    cn0
    @16
    @68
    @19
    @68
    @16
    @19
    vk
    vy
    cS
    caddc
    @66
    @13
    cc0
    @11
    cvv
    @37
    @19
    @11
    cn0
    cc0
    cuz
    cfv
    #
    wph
    @18
    simpr
    nn0uz
    syl6eleq
    @19
    vk
    cv
    #
    cc0
    @11
    cfz
    co
    wcel
    #
    wa
    #
    @71
    cn0
    wcel
    #
    vy
    cS
    @71
    @13
    cfv
    #
    cmpt
    #
    cvv
    wcel
    #
    @71
    @66
    cfv
    #
    @76
    wceq
    #
    @72
    @74
    @19
    @71
    @11
    elfznn0
    adantl
    @73
    @34
    @77
    wph
    @34
    @18
    @72
    @36
    ad2antrr
    vy
    cS
    @75
    cvv
    mptexg
    #
    syl
    vm
    @71
    @65
    @76
    cn0
    cvv
    @66
    vm
    vk
    weq
    #
    @65
    vy
    cS
    @61
    @13
    cfv
    #
    cmpt
    @76
    vw
    vy
    cS
    @64
    @82
    vw
    vy
    weq
    @61
    @63
    @13
    @62
    @12
    cG
    fveq2
    fveq1d
    cbvmptv
    @81
    vy
    cS
    @82
    @75
    @61
    @71
    @13
    fveq2
    mpteq2dv
    syl5eq
    @66
    eqid
    #
    fvmptg
    #
    syl2anc
    seqof
    eqcomd
    mpteq2dva
    pserulm.h
    @67
    cn0
    wfn
    #
    @67
    @69
    wceq
    @85
    @67
    @70
    wfn
    #
    cc0
    cz
    wcel
    @86
    0z
    @60
    @66
    cc0
    seqfn
    ax-mp
    cn0
    @70
    @67
    nn0uz
    fneq2i
    mpbir
    vi
    cn0
    @67
    dffn5
    mpbi
    3eqtr4g
    adantr
    @59
    vz
    cS
    vk
    @66
    cabs
    cM
    cG
    cfv
    #
    ccom
    #
    cc0
    cvv
    cvv
    cn0
    nn0uz
    @59
    0zd
    wph
    @34
    @56
    @36
    adantr
    wph
    cn0
    @17
    @66
    wf
    @56
    wph
    vm
    cn0
    @65
    @17
    @66
    wph
    @61
    cn0
    wcel
    #
    wa
    #
    @65
    @17
    wcel
    #
    cS
    cc
    @65
    wf
    #
    @90
    vw
    cS
    @64
    cc
    @65
    wph
    @62
    cS
    wcel
    #
    @89
    @64
    cc
    wcel
    wph
    @93
    wa
    #
    cn0
    cc
    @61
    @63
    @94
    vx
    cA
    vn
    cG
    @62
    pserf.g
    wph
    @26
    @93
    pserf.a
    adantr
    wph
    cS
    cc
    @62
    @28
    sselda
    psergf
    ffvelrnda
    an32s
    @65
    eqid
    fmptd
    @90
    @33
    @34
    @91
    @92
    wb
    cnex
    wph
    @34
    @89
    @36
    adantr
    cc
    cS
    @65
    cvv
    cvv
    elmapg
    sylancr
    mpbird
    @83
    fmptd
    adantr
    @88
    cvv
    wcel
    @59
    cabs
    @87
    @51
    @33
    cabs
    cvv
    wcel
    absf
    cnex
    cc
    cr
    cvv
    cabs
    fex
    mp2an
    cM
    cG
    fvex
    coex
    a1i
    @59
    cn0
    cr
    @71
    @88
    @59
    @51
    cn0
    cc
    @87
    wf
    #
    cn0
    cr
    @88
    wf
    absf
    @59
    vx
    cA
    vn
    cG
    cM
    pserf.g
    wph
    @26
    @56
    pserf.a
    adantr
    #
    @59
    cM
    wph
    @52
    @56
    pserulm.m
    adantr
    recnd
    #
    psergf
    #
    cn0
    cc
    cr
    cabs
    @87
    fco
    sylancr
    ffvelrnda
    @59
    @74
    vz
    cv
    #
    cS
    wcel
    #
    wa
    #
    wa
    #
    @71
    cA
    cfv
    #
    @99
    @71
    cexp
    co
    #
    cmul
    co
    #
    cabs
    cfv
    #
    @103
    cM
    @71
    cexp
    co
    #
    cmul
    co
    #
    cabs
    cfv
    #
    @99
    @78
    cfv
    #
    cabs
    cfv
    @71
    @88
    cfv
    #
    cle
    @102
    @103
    cabs
    cfv
    #
    @104
    cabs
    cfv
    #
    cmul
    co
    @112
    @107
    cabs
    cfv
    #
    cmul
    co
    @106
    @109
    cle
    @102
    @113
    @114
    @112
    @102
    @104
    @102
    @99
    @71
    @102
    cS
    cc
    @99
    wph
    @35
    @56
    @101
    @28
    ad2antrr
    @59
    @74
    @100
    simprr
    #
    sseldd
    #
    @59
    @74
    @100
    simprl
    #
    expcld
    #
    abscld
    @102
    @107
    @102
    cM
    @71
    @59
    cM
    cc
    wcel
    #
    @101
    @97
    adantr
    #
    @117
    expcld
    #
    abscld
    @102
    @103
    @102
    cn0
    cc
    @71
    cA
    wph
    @26
    @56
    @101
    pserf.a
    ad2antrr
    @117
    ffvelrnd
    #
    abscld
    @102
    @103
    @122
    absge0d
    @102
    @99
    cabs
    cfv
    #
    @71
    cexp
    co
    #
    @107
    @113
    @114
    cle
    @102
    @123
    cr
    wcel
    @52
    @74
    cc0
    @123
    cle
    wbr
    @123
    cM
    cle
    wbr
    #
    @124
    @107
    cle
    wbr
    @102
    @99
    @116
    abscld
    wph
    @52
    @56
    @101
    pserulm.m
    ad2antrr
    @117
    @102
    @99
    @116
    absge0d
    @102
    @100
    @45
    vy
    cS
    wral
    #
    @125
    @115
    wph
    @126
    @56
    @101
    wph
    @45
    vy
    cS
    @54
    ralrimiva
    ad2antrr
    @45
    @125
    vy
    @99
    cS
    vy
    vz
    weq
    #
    @42
    @123
    cM
    cle
    @12
    @99
    cabs
    fveq2
    breq1d
    rspcv
    sylc
    @123
    cM
    @71
    leexp1a
    syl32anc
    @102
    @99
    @71
    @116
    @117
    absexpd
    @102
    @114
    cM
    cabs
    cfv
    #
    @71
    cexp
    co
    @107
    @102
    cM
    @71
    @120
    @117
    absexpd
    @102
    @128
    cM
    @71
    cexp
    @59
    @128
    cM
    wceq
    #
    @101
    wph
    @52
    @56
    @129
    pserulm.m
    cM
    absid
    sylan
    #
    adantr
    oveq1d
    eqtrd
    3brtr4d
    lemul2ad
    @102
    @103
    @104
    @122
    @118
    absmuld
    @102
    @103
    @107
    @122
    @121
    absmuld
    3brtr4d
    @102
    @110
    @105
    cabs
    @102
    @110
    @99
    @76
    cfv
    #
    @71
    @99
    cG
    cfv
    #
    cfv
    #
    @105
    @102
    @99
    @78
    @76
    @102
    @74
    @77
    @79
    @117
    @102
    @34
    @77
    wph
    @34
    @56
    @101
    @36
    ad2antrr
    @80
    syl
    @84
    syl2anc
    fveq1d
    @100
    @131
    @133
    wceq
    @59
    @74
    vy
    @99
    @75
    @133
    cS
    @76
    @127
    @71
    @13
    @132
    @12
    @99
    cG
    fveq2
    fveq1d
    @76
    eqid
    @71
    @132
    fvex
    fvmpt
    ad2antll
    @102
    @99
    cc
    wcel
    @74
    @133
    @105
    wceq
    @116
    @117
    vx
    cA
    vn
    cG
    @71
    @99
    pserf.g
    pserval2
    syl2anc
    3eqtrd
    fveq2d
    @102
    @111
    @71
    @87
    cfv
    #
    cabs
    cfv
    #
    @109
    @102
    @95
    @74
    @111
    @135
    wceq
    @59
    @95
    @101
    @98
    adantr
    @117
    cn0
    cc
    @71
    cabs
    @87
    fvco3
    syl2anc
    @102
    @134
    @108
    cabs
    @102
    @119
    @74
    @134
    @108
    wceq
    @120
    @117
    vx
    cA
    vn
    cG
    @71
    cM
    pserf.g
    pserval2
    syl2anc
    fveq2d
    eqtrd
    3brtr4d
    @59
    caddc
    vi
    cn0
    @11
    @11
    @87
    cfv
    #
    cabs
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    cc0
    cseq
    cli
    cdm
    #
    wcel
    caddc
    @88
    cc0
    cseq
    @140
    wcel
    @59
    vx
    cA
    cR
    vm
    vn
    cG
    @139
    cM
    vr
    pserf.g
    @96
    pserf.r
    @97
    @59
    @128
    cM
    cR
    clt
    @130
    wph
    @55
    @56
    pserulm.l
    adantr
    eqbrtrd
    vi
    vm
    cn0
    @138
    @61
    @61
    @87
    cfv
    #
    cabs
    cfv
    #
    cmul
    co
    vi
    vm
    weq
    #
    @11
    @61
    @137
    @142
    cmul
    @143
    id
    @143
    @136
    @141
    cabs
    @11
    @61
    @87
    fveq2
    fveq2d
    oveq12d
    cbvmptv
    radcnvlt1
    simprd
    mtest
    eqeltrd
    wph
    @58
    @1
    @58
    cH
    vf
    cv
    #
    @0
    wbr
    #
    vf
    wex
    #
    wph
    @1
    @58
    @146
    vf
    cH
    @0
    @57
    eldmg
    ibi
    wph
    @145
    @1
    vf
    wph
    @145
    @1
    wph
    @145
    wa
    #
    cH
    @144
    cF
    @0
    wph
    @145
    simpr
    @147
    @144
    vy
    cS
    @12
    @144
    cfv
    #
    cmpt
    #
    cF
    @147
    vy
    cS
    cc
    @144
    @145
    cS
    cc
    @144
    wf
    wph
    cS
    cH
    @144
    ulmcl
    adantl
    feqmptd
    @147
    cF
    vy
    cS
    @40
    cmpt
    @149
    pserf.f
    @147
    vy
    cS
    @40
    @148
    @147
    @22
    wa
    #
    @39
    @148
    vj
    @13
    cc0
    cn0
    nn0uz
    @150
    0zd
    #
    @150
    @41
    wa
    @39
    eqidd
    @150
    cn0
    cc
    @25
    @13
    wph
    @22
    cn0
    cc
    @13
    wf
    @145
    @30
    adantlr
    ffvelrnda
    @150
    @12
    cS
    vi
    cH
    @144
    @14
    cc0
    cvv
    cn0
    nn0uz
    @151
    wph
    cn0
    @17
    cH
    wf
    @145
    @22
    @38
    ad2antrr
    @147
    @22
    simpr
    @14
    cvv
    wcel
    @150
    caddc
    @13
    cc0
    seqex
    a1i
    @150
    @18
    wa
    #
    @12
    @11
    cH
    cfv
    #
    cfv
    @12
    @16
    cfv
    #
    @15
    @152
    @12
    @153
    @16
    @152
    @18
    @16
    cvv
    wcel
    #
    @153
    @16
    wceq
    @150
    @18
    simpr
    @152
    @34
    @155
    wph
    @34
    @145
    @22
    @18
    @36
    ad3antrrr
    vy
    cS
    @15
    cvv
    mptexg
    syl
    vi
    cn0
    @16
    cvv
    cH
    pserulm.h
    fvmpt2
    syl2anc
    fveq1d
    @152
    @22
    @15
    cvv
    wcel
    @154
    @15
    wceq
    @147
    @22
    @18
    simplr
    @11
    @14
    fvex
    vy
    cS
    @15
    cvv
    @16
    @32
    fvmpt2
    sylancl
    eqtrd
    wph
    @145
    @22
    simplr
    ulmclm
    isumclim
    mpteq2dva
    syl5eq
    eqtr4d
    breqtrd
    ex
    exlimdv
    syl5
    imp
    syldan
    pserulm.m
    wph
    0red
    ltlecasei
end
