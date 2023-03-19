include "csuc.mm"
include "cfv.mm"
include "com.mm"
include "coe.mm"
include "co.mm"
include "comu.mm"
include "coa.mm"
include "wf1o.mm"
include "cv.mm"
include "cmpt.mm"
include "ccnv.mm"
include "cun.mm"
include "con0.mm"
include "wcel.mm"
include "omelon.mm"
include "c0.mm"
include "csupp.mm"
include "cdm.mm"
include "suppssdm.mm"
include "wf.mm"
include "wceq.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wa.mm"
include "ccnf.mm"
include "a1i.mm"
include "cantnff1o.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "3syl.mm"
include "ffvelrnd.mm"
include "syl5eqel.mm"
include "cantnfs.mm"
include "mpbid.mm"
include "simpld.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "cep.mm"
include "oif.mm"
include "ffvelrni.mm"
include "sseldd.mm"
include "onelon.mm"
include "syl2anc.mm"
include "oecl.mm"
include "sylancr.mm"
include "nnon.mm"
include "omcl.mm"
include "wwe.mm"
include "cantnfcl.mm"
include "simprd.mm"
include "elnn.mm"
include "cvv.mm"
include "cantnfvalf.mm"
include "eqid.mm"
include "oacomf1o.mm"
include "wb.mm"
include "cmpt2.mm"
include "seqomsuc.mm"
include "nfcv.mm"
include "weq.mm"
include "oveq2.mm"
include "cbvmptv.mm"
include "simpl.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "syl5eq.mm"
include "simpr.mm"
include "dmeqd.mm"
include "oveq1d.mm"
include "mpteq12dv.mm"
include "cnveqd.mm"
include "uneq12d.mm"
include "cbvmpt2.mm"
include "simprl.mm"
include "f1odm.mm"
include "sylan9eqr.mm"
include "elex.mm"
include "fvexd.mm"
include "ovex.mm"
include "mptex.mm"
include "fvex.mm"
include "cnvex.mm"
include "unex.mm"
include "ovmpt2d.mm"
include "eqtrd.mm"
include "f1oeq1.mm"
include "mpbird.mm"
include "cseqom.mm"
include "oveq1i.mm"
include "mpt2eq3ia.mm"
include "seqomeq12.mm"
include "mp2an.mm"
include "eqtri.mm"
include "cantnfsuc.mm"
include "syl21anc.mm"
include "f1oeq2.mm"
include "wss.mm"
include "cima.mm"
include "sssucid.mm"
include "sseldi.mm"
include "wral.mm"
include "epelg.mm"
include "biimpar.mm"
include "wiso.mm"
include "ovexd.mm"
include "oiiso.mm"
include "adantr.mm"
include "word.mm"
include "oicl.mm"
include "ordelss.mm"
include "sselda.mm"
include "isorel.mm"
include "syl12anc.mm"
include "epelc.mm"
include "sylib.mm"
include "ralrimiva.mm"
include "wfun.mm"
include "ffun.mm"
include "ax-mp.mm"
include "funimass4.mm"
include "w3a.mm"
include "simpll.mm"
include "simplr.mm"
include "peano1.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "cantnflt.mm"
include "syl23anc.mm"
include "wne.mm"
include "wfn.mm"
include "ffn.mm"
include "0ex.mm"
include "elsuppfn.mm"
include "syl3anc.mm"
include "syl6bi.mm"
include "mpd.mm"
include "on0eln0.mm"
include "omword1.mm"
include "oaabs2.mm"
include "f1oeq3.mm"

theorem cnfcomlem
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cM: class M
  let cO: class O
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let cW: class W
  assume cnfcom.s: |- S = dom ( _om CNF A )
  assume cnfcom.a: |- ( ph -> A e. On )
  assume cnfcom.b: |- ( ph -> B e. ( _om ^o A ) )
  assume cnfcom.f: |- F = ( `' ( _om CNF A ) ` B )
  assume cnfcom.g: |- G = OrdIso ( _E , ( F supp (/) ) )
  assume cnfcom.h: |- H = seqom ( ( k e. _V , z e. _V |-> ( M +o z ) ) , (/) )
  assume cnfcom.t: |- T = seqom ( ( k e. _V , f e. _V |-> K ) , (/) )
  assume cnfcom.m: |- M = ( ( _om ^o ( G ` k ) ) .o ( F ` ( G ` k ) ) )
  assume cnfcom.k: |- K = ( ( x e. M |-> ( dom f +o x ) ) u. `' ( x e. dom f |-> ( M +o x ) ) )
  assume cnfcom.1: |- ( ph -> I e. dom G )
  assume cnfcom.2: |- ( ph -> O e. ( _om ^o ( G ` I ) ) )
  assume cnfcom.3: |- ( ph -> ( T ` I ) : ( H ` I ) -1-1-onto-> O )

  disjoint k x
  disjoint k z
  disjoint A k
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint I k
  disjoint I x
  disjoint I z
  disjoint M x
  disjoint f k
  disjoint f x
  disjoint f z
  disjoint F f
  disjoint F k
  disjoint F x
  disjoint F z
  disjoint T z
  disjoint G f
  disjoint G k
  disjoint G x
  disjoint G z
  disjoint H f
  disjoint H x
  disjoint S k
  disjoint S z
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k y
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint I u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint I v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint I w
  disjoint x y
  disjoint y z
  disjoint I y
  disjoint M y
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f y
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F y
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint T u
  disjoint T v
  disjoint T w
  disjoint T y
  disjoint W u
  disjoint W v
  disjoint W x
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G y
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint H y
  assert |- ( ph -> ( T ` suc I ) : ( H ` suc I ) -1-1-onto-> ( ( _om ^o ( G ` I ) ) .o ( F ` ( G ` I ) ) ) )

  proof
    wph
    cI
    csuc
    #
    cH
    cfv
    #
    cI
    cH
    cfv
    #
    com
    cI
    cG
    cfv
    #
    coe
    co
    #
    @3
    cF
    cfv
    #
    comu
    co
    #
    coa
    co
    #
    @0
    cT
    cfv
    #
    wf1o
    #
    @1
    @6
    @8
    wf1o
    #
    wph
    @9
    @6
    @2
    coa
    co
    #
    @7
    @8
    wf1o
    #
    wph
    @12
    @11
    @7
    vy
    @6
    @2
    vy
    cv
    #
    coa
    co
    #
    cmpt
    #
    vy
    @2
    @6
    @13
    coa
    co
    #
    cmpt
    #
    ccnv
    #
    cun
    #
    wf1o
    #
    wph
    @6
    con0
    wcel
    #
    @2
    con0
    wcel
    #
    @20
    wph
    @4
    con0
    wcel
    #
    @5
    con0
    wcel
    #
    @21
    wph
    com
    con0
    wcel
    #
    @3
    con0
    wcel
    #
    @23
    omelon
    wph
    cA
    con0
    wcel
    #
    @3
    cA
    wcel
    #
    @26
    cnfcom.a
    wph
    cF
    c0
    csupp
    co
    #
    cA
    @3
    wph
    cF
    cdm
    #
    @29
    cA
    cF
    c0
    suppssdm
    wph
    cA
    com
    cF
    wf
    #
    @30
    cA
    wceq
    wph
    @31
    cF
    c0
    cfsupp
    wbr
    #
    wph
    cF
    cS
    wcel
    #
    @31
    @32
    wa
    wph
    cF
    cB
    com
    cA
    ccnf
    co
    #
    ccnv
    #
    cfv
    cS
    cnfcom.f
    wph
    com
    cA
    coe
    co
    #
    cS
    cB
    @35
    wph
    cS
    @36
    @34
    wf1o
    @36
    cS
    @35
    wf1o
    @36
    cS
    @35
    wf
    wph
    com
    cA
    cS
    cnfcom.s
    @25
    wph
    omelon
    a1i
    #
    cnfcom.a
    cantnff1o
    cS
    @36
    @34
    f1ocnv
    @36
    cS
    @35
    f1of
    3syl
    cnfcom.b
    ffvelrnd
    syl5eqel
    #
    wph
    com
    cA
    cS
    cF
    cnfcom.s
    @37
    cnfcom.a
    cantnfs
    mpbid
    simpld
    #
    cA
    com
    cF
    fdm
    syl
    syl5sseq
    wph
    cI
    cG
    cdm
    #
    wcel
    #
    @3
    @29
    wcel
    #
    cnfcom.1
    @40
    @29
    cI
    cG
    @29
    cep
    cG
    cnfcom.g
    oif
    #
    ffvelrni
    syl
    #
    sseldd
    #
    cA
    @3
    onelon
    syl2anc
    #
    com
    @3
    oecl
    sylancr
    #
    wph
    @5
    com
    wcel
    @24
    wph
    cA
    com
    @3
    cF
    @39
    @45
    ffvelrnd
    @5
    nnon
    syl
    #
    @4
    @5
    omcl
    syl2anc
    #
    wph
    cI
    com
    wcel
    #
    @22
    wph
    @41
    @40
    com
    wcel
    #
    @50
    cnfcom.1
    wph
    @29
    cep
    wwe
    #
    @51
    wph
    com
    cA
    cS
    cF
    cG
    cnfcom.s
    @37
    cnfcom.a
    cnfcom.g
    @38
    cantnfcl
    #
    simprd
    cI
    @40
    elnn
    syl2anc
    #
    com
    con0
    cI
    cH
    vz
    cvv
    cvv
    cM
    vz
    cv
    #
    vk
    cH
    cnfcom.h
    cantnfvalf
    ffvelrni
    syl
    vy
    @6
    @2
    @19
    @19
    eqid
    oacomf1o
    syl2anc
    wph
    @8
    @19
    wceq
    @12
    @20
    wb
    wph
    @8
    cI
    cI
    cT
    cfv
    #
    vk
    vf
    cvv
    cvv
    cK
    cmpt2
    #
    co
    #
    @19
    wph
    @50
    @8
    @58
    wceq
    @54
    cI
    @57
    cT
    c0
    cnfcom.t
    seqomsuc
    syl
    wph
    vu
    vv
    cI
    @56
    cvv
    cvv
    vy
    com
    vu
    cv
    #
    cG
    cfv
    #
    coe
    co
    #
    @60
    cF
    cfv
    #
    comu
    co
    #
    vv
    cv
    #
    cdm
    #
    @13
    coa
    co
    #
    cmpt
    #
    vy
    @65
    @63
    @13
    coa
    co
    #
    cmpt
    #
    ccnv
    #
    cun
    #
    @19
    @57
    cvv
    @57
    vu
    vv
    cvv
    cvv
    @71
    cmpt2
    wceq
    wph
    vk
    vf
    vu
    vv
    cvv
    cvv
    cK
    @71
    vu
    cK
    nfcv
    vv
    cK
    nfcv
    vk
    @71
    nfcv
    vf
    @71
    nfcv
    vk
    vu
    weq
    #
    vf
    vv
    weq
    #
    wa
    #
    cK
    vx
    cM
    vf
    cv
    #
    cdm
    #
    vx
    cv
    #
    coa
    co
    #
    cmpt
    #
    vx
    @76
    cM
    @77
    coa
    co
    #
    cmpt
    #
    ccnv
    #
    cun
    @71
    cnfcom.k
    @74
    @79
    @67
    @82
    @70
    @74
    @79
    vy
    cM
    @76
    @13
    coa
    co
    #
    cmpt
    @67
    vx
    vy
    cM
    @78
    @83
    @77
    @13
    @76
    coa
    oveq2
    cbvmptv
    @74
    vy
    cM
    @83
    @63
    @66
    @74
    cM
    com
    vk
    cv
    #
    cG
    cfv
    #
    coe
    co
    #
    @85
    cF
    cfv
    #
    comu
    co
    #
    @63
    cnfcom.m
    @74
    @86
    @61
    @87
    @62
    comu
    @74
    @85
    @60
    com
    coe
    @74
    @84
    @59
    cG
    @72
    @73
    simpl
    fveq2d
    #
    oveq2d
    @74
    @85
    @60
    cF
    @89
    fveq2d
    oveq12d
    syl5eq
    #
    @74
    @76
    @65
    @13
    coa
    @74
    @75
    @64
    @72
    @73
    simpr
    dmeqd
    #
    oveq1d
    mpteq12dv
    syl5eq
    @74
    @81
    @69
    @74
    @81
    vy
    @76
    cM
    @13
    coa
    co
    #
    cmpt
    @69
    vx
    vy
    @76
    @80
    @92
    @77
    @13
    cM
    coa
    oveq2
    cbvmptv
    @74
    vy
    @76
    @92
    @65
    @68
    @91
    @74
    cM
    @63
    @13
    coa
    @90
    oveq1d
    mpteq12dv
    syl5eq
    cnveqd
    uneq12d
    syl5eq
    cbvmpt2
    a1i
    wph
    @59
    cI
    wceq
    #
    @64
    @56
    wceq
    #
    wa
    #
    wa
    #
    @67
    @15
    @70
    @18
    @96
    vy
    @63
    @66
    @6
    @14
    @96
    @61
    @4
    @62
    @5
    comu
    @96
    @60
    @3
    com
    coe
    @96
    @59
    cI
    cG
    wph
    @93
    @94
    simprl
    fveq2d
    #
    oveq2d
    @96
    @60
    @3
    cF
    @97
    fveq2d
    oveq12d
    #
    @96
    @65
    @2
    @13
    coa
    @95
    wph
    @65
    @56
    cdm
    #
    @2
    @95
    @64
    @56
    @93
    @94
    simpr
    dmeqd
    wph
    @2
    cO
    @56
    wf1o
    @99
    @2
    wceq
    cnfcom.3
    @2
    cO
    @56
    f1odm
    syl
    sylan9eqr
    #
    oveq1d
    mpteq12dv
    @96
    @69
    @17
    @96
    vy
    @65
    @68
    @2
    @16
    @100
    @96
    @63
    @6
    @13
    coa
    @98
    oveq1d
    mpteq12dv
    cnveqd
    uneq12d
    wph
    @41
    cI
    cvv
    wcel
    cnfcom.1
    cI
    @40
    elex
    syl
    wph
    cI
    cT
    fvexd
    @19
    cvv
    wcel
    wph
    @15
    @18
    vy
    @6
    @14
    @4
    @5
    comu
    ovex
    mptex
    @17
    vy
    @2
    @16
    cI
    cH
    fvex
    mptex
    cnvex
    unex
    a1i
    ovmpt2d
    eqtrd
    @11
    @7
    @8
    @19
    f1oeq1
    syl
    mpbird
    wph
    @1
    @11
    wceq
    #
    @9
    @12
    wb
    wph
    @27
    @33
    @50
    @101
    cnfcom.a
    @38
    @54
    @27
    @33
    wa
    #
    vz
    com
    cA
    cS
    vk
    cF
    cG
    cH
    cI
    cnfcom.s
    @25
    @102
    omelon
    a1i
    @27
    @33
    simpl
    cnfcom.g
    @27
    @33
    simpr
    cH
    vk
    vz
    cvv
    cvv
    cM
    @55
    coa
    co
    #
    cmpt2
    #
    c0
    cseqom
    #
    vk
    vz
    cvv
    cvv
    @88
    @55
    coa
    co
    #
    cmpt2
    #
    c0
    cseqom
    #
    cnfcom.h
    @104
    @107
    wceq
    c0
    c0
    wceq
    @105
    @108
    wceq
    vk
    vz
    cvv
    cvv
    @103
    @106
    @103
    @106
    wceq
    @84
    cvv
    wcel
    @55
    cvv
    wcel
    wa
    cM
    @88
    @55
    coa
    cnfcom.m
    oveq1i
    a1i
    mpt2eq3ia
    c0
    eqid
    @104
    @107
    c0
    c0
    seqomeq12
    mp2an
    eqtri
    #
    cantnfsuc
    syl21anc
    @1
    @11
    @7
    @8
    f1oeq2
    syl
    mpbird
    wph
    @7
    @6
    wceq
    #
    @9
    @10
    wb
    wph
    @2
    @4
    wcel
    #
    @21
    @4
    @6
    wss
    #
    @110
    wph
    @27
    @33
    cI
    @40
    csuc
    #
    wcel
    #
    @26
    cG
    cI
    cima
    @3
    wss
    #
    @111
    cnfcom.a
    @38
    wph
    @40
    @113
    cI
    @40
    sssucid
    cnfcom.1
    sseldi
    @46
    wph
    @115
    @13
    cG
    cfv
    #
    @3
    wcel
    #
    vy
    cI
    wral
    #
    wph
    @117
    vy
    cI
    wph
    @13
    cI
    wcel
    #
    wa
    #
    @116
    @3
    cep
    wbr
    #
    @117
    @120
    @13
    cI
    cep
    wbr
    #
    @121
    wph
    @122
    @119
    wph
    @41
    @122
    @119
    wb
    cnfcom.1
    @13
    cI
    @40
    epelg
    syl
    biimpar
    @120
    @40
    @29
    cep
    cep
    cG
    wiso
    #
    @13
    @40
    wcel
    @41
    @122
    @121
    wb
    wph
    @123
    @119
    wph
    @29
    cvv
    wcel
    @52
    @123
    wph
    cF
    c0
    csupp
    ovexd
    wph
    @52
    @51
    @53
    simpld
    @29
    cep
    cG
    cvv
    cnfcom.g
    oiiso
    syl2anc
    adantr
    wph
    cI
    @40
    @13
    wph
    @40
    word
    @41
    cI
    @40
    wss
    #
    @29
    cep
    cG
    cnfcom.g
    oicl
    cnfcom.1
    @40
    cI
    ordelss
    sylancr
    #
    sselda
    wph
    @41
    @119
    cnfcom.1
    adantr
    @40
    @29
    @13
    cI
    cep
    cep
    cG
    isorel
    syl12anc
    mpbid
    @116
    @3
    cI
    cG
    fvex
    epelc
    sylib
    ralrimiva
    wph
    cG
    wfun
    #
    @124
    @115
    @118
    wb
    @40
    @29
    cG
    wf
    @126
    @43
    @40
    @29
    cG
    ffun
    ax-mp
    @125
    vy
    cI
    @3
    cG
    funimass4
    sylancr
    mpbird
    @102
    @114
    @26
    @115
    w3a
    #
    wa
    #
    vz
    com
    cA
    @3
    cS
    vk
    cF
    cG
    cH
    cI
    cnfcom.s
    @25
    @128
    omelon
    a1i
    @27
    @33
    @127
    simpll
    cnfcom.g
    @27
    @33
    @127
    simplr
    @109
    c0
    com
    wcel
    @128
    peano1
    a1i
    @102
    @114
    @26
    @115
    simpr1
    @102
    @114
    @26
    @115
    simpr2
    @102
    @114
    @26
    @115
    simpr3
    cantnflt
    syl23anc
    @49
    wph
    @23
    @24
    c0
    @5
    wcel
    #
    @112
    @47
    @48
    wph
    @129
    @5
    c0
    wne
    #
    wph
    @42
    @130
    @44
    wph
    @42
    @28
    @130
    wa
    #
    @130
    wph
    cF
    cA
    wfn
    #
    @27
    c0
    cvv
    wcel
    #
    @42
    @131
    wb
    wph
    @31
    @132
    @39
    cA
    com
    cF
    ffn
    syl
    cnfcom.a
    @133
    wph
    0ex
    a1i
    @3
    cF
    con0
    cvv
    cA
    c0
    elsuppfn
    syl3anc
    @28
    @130
    simpr
    syl6bi
    mpd
    wph
    @24
    @129
    @130
    wb
    @48
    @5
    on0eln0
    syl
    mpbird
    @4
    @5
    omword1
    syl21anc
    @2
    @6
    @3
    oaabs2
    syl21anc
    @7
    @6
    @1
    @8
    f1oeq3
    syl
    mpbid
end
