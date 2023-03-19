include "cdm.mm"
include "wcel.mm"
include "csuc.mm"
include "cfv.mm"
include "com.mm"
include "coe.mm"
include "co.mm"
include "comu.mm"
include "wf1o.mm"
include "wi.mm"
include "c0.mm"
include "csupp.mm"
include "cep.mm"
include "wwe.mm"
include "con0.mm"
include "omelon.mm"
include "a1i.mm"
include "ccnf.mm"
include "ccnv.mm"
include "wf.mm"
include "cantnff1o.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "3syl.mm"
include "ffvelrnd.mm"
include "syl5eqel.mm"
include "cantnfcl.mm"
include "simprd.mm"
include "elnn.mm"
include "syl2anc.mm"
include "cv.mm"
include "wceq.mm"
include "eleq1.mm"
include "suceq.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "f1oeq123d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "wa.mm"
include "adantr.mm"
include "simpr.mm"
include "wss.mm"
include "suppssdm.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cantnfs.mm"
include "mpbid.mm"
include "simpld.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "onss.mm"
include "sstrd.mm"
include "oif.mm"
include "ffvelrni.mm"
include "ssel2.mm"
include "syl2an.mm"
include "peano1.mm"
include "oen0.mm"
include "syl21anc.mm"
include "cvv.mm"
include "0ex.mm"
include "cmpt2.mm"
include "seqom0g.mm"
include "ax-mp.mm"
include "f1o0.mm"
include "wb.mm"
include "coa.mm"
include "f1oeq2.mm"
include "mp2b.mm"
include "mpbir.mm"
include "f1oeq1.mm"
include "mpbiri.mm"
include "mp1i.mm"
include "cnfcomlem.mm"
include "ex.mm"
include "wtr.mm"
include "word.mm"
include "oicl.mm"
include "ordtr.mm"
include "trsuc.mm"
include "mpan.mm"
include "imim1i.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "ad2antrl.mm"
include "sseldd.mm"
include "eloni.mm"
include "vex.mm"
include "sucid.mm"
include "wiso.mm"
include "ssexd.mm"
include "oiiso.mm"
include "isorel.mm"
include "syl12anc.mm"
include "sucex.mm"
include "epelc.mm"
include "fvex.mm"
include "3bitr3g.mm"
include "mpbii.mm"
include "ordsucss.mm"
include "sylc.mm"
include "suceloni.mm"
include "oewordi.mm"
include "syl31anc.mm"
include "mpd.mm"
include "nnon.mm"
include "oecl.mm"
include "omord2.mm"
include "oesuc.mm"
include "eleqtrrd.mm"
include "simprr.mm"
include "exp32.mm"
include "a2d.mm"
include "syl5.mm"
include "expcom.mm"
include "finds2.mm"
include "vtoclga.mm"
include "mpcom.mm"

theorem cnfcom
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
    cG
    cdm
    #
    wcel
    #
    cI
    csuc
    #
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
    @4
    cF
    cfv
    #
    comu
    co
    #
    @2
    cT
    cfv
    #
    wf1o
    #
    cnfcom.1
    cI
    com
    wcel
    #
    wph
    @1
    @9
    wi
    #
    wph
    @1
    @0
    com
    wcel
    #
    @10
    cnfcom.1
    wph
    cF
    c0
    csupp
    co
    #
    cep
    wwe
    #
    @12
    wph
    com
    cA
    cS
    cF
    cG
    cnfcom.s
    com
    con0
    wcel
    #
    wph
    omelon
    a1i
    #
    cnfcom.a
    cnfcom.g
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
    @18
    wph
    cS
    @19
    @17
    wf1o
    @19
    cS
    @18
    wf1o
    @19
    cS
    @18
    wf
    wph
    com
    cA
    cS
    cnfcom.s
    @16
    cnfcom.a
    cantnff1o
    cS
    @19
    @17
    f1ocnv
    @19
    cS
    @18
    f1of
    3syl
    cnfcom.b
    ffvelrnd
    syl5eqel
    #
    cantnfcl
    #
    simprd
    cI
    @0
    elnn
    syl2anc
    wph
    vw
    cv
    #
    @0
    wcel
    #
    @22
    csuc
    #
    cH
    cfv
    #
    com
    @22
    cG
    cfv
    #
    coe
    co
    #
    @26
    cF
    cfv
    #
    comu
    co
    #
    @24
    cT
    cfv
    #
    wf1o
    #
    wi
    #
    wi
    wph
    @11
    wi
    vw
    cI
    com
    @22
    cI
    wceq
    #
    @32
    @11
    wph
    @33
    @23
    @1
    @31
    @9
    @22
    cI
    @0
    eleq1
    @33
    @25
    @3
    @29
    @7
    @30
    @8
    @33
    @24
    @2
    cT
    @22
    cI
    suceq
    #
    fveq2d
    @33
    @24
    @2
    cH
    @34
    fveq2d
    @33
    @27
    @5
    @28
    @6
    comu
    @33
    @26
    @4
    com
    coe
    @22
    cI
    cG
    fveq2
    #
    oveq2d
    @33
    @26
    @4
    cF
    @35
    fveq2d
    oveq12d
    f1oeq123d
    imbi12d
    imbi2d
    @32
    c0
    @0
    wcel
    #
    c0
    csuc
    #
    cH
    cfv
    #
    com
    c0
    cG
    cfv
    #
    coe
    co
    #
    @39
    cF
    cfv
    #
    comu
    co
    #
    @37
    cT
    cfv
    #
    wf1o
    #
    wi
    vy
    cv
    #
    @0
    wcel
    #
    @45
    csuc
    #
    cH
    cfv
    #
    com
    @45
    cG
    cfv
    #
    coe
    co
    #
    @49
    cF
    cfv
    #
    comu
    co
    #
    @47
    cT
    cfv
    #
    wf1o
    #
    wi
    #
    @47
    @0
    wcel
    #
    @47
    csuc
    #
    cH
    cfv
    #
    com
    @47
    cG
    cfv
    #
    coe
    co
    #
    @59
    cF
    cfv
    #
    comu
    co
    #
    @57
    cT
    cfv
    #
    wf1o
    #
    wi
    #
    wph
    vw
    vy
    @22
    c0
    wceq
    #
    @23
    @36
    @31
    @44
    @22
    c0
    @0
    eleq1
    @66
    @25
    @38
    @29
    @42
    @30
    @43
    @66
    @24
    @37
    cT
    @22
    c0
    suceq
    #
    fveq2d
    @66
    @24
    @37
    cH
    @67
    fveq2d
    @66
    @27
    @40
    @28
    @41
    comu
    @66
    @26
    @39
    com
    coe
    @22
    c0
    cG
    fveq2
    #
    oveq2d
    @66
    @26
    @39
    cF
    @68
    fveq2d
    oveq12d
    f1oeq123d
    imbi12d
    @22
    @45
    wceq
    #
    @23
    @46
    @31
    @54
    @22
    @45
    @0
    eleq1
    @69
    @25
    @48
    @29
    @52
    @30
    @53
    @69
    @24
    @47
    cT
    @22
    @45
    suceq
    #
    fveq2d
    @69
    @24
    @47
    cH
    @70
    fveq2d
    @69
    @27
    @50
    @28
    @51
    comu
    @69
    @26
    @49
    com
    coe
    @22
    @45
    cG
    fveq2
    #
    oveq2d
    @69
    @26
    @49
    cF
    @71
    fveq2d
    oveq12d
    f1oeq123d
    imbi12d
    @22
    @47
    wceq
    #
    @23
    @56
    @31
    @64
    @22
    @47
    @0
    eleq1
    @72
    @25
    @58
    @29
    @62
    @30
    @63
    @72
    @24
    @57
    cT
    @22
    @47
    suceq
    #
    fveq2d
    @72
    @24
    @57
    cH
    @73
    fveq2d
    @72
    @27
    @60
    @28
    @61
    comu
    @72
    @26
    @59
    com
    coe
    @22
    @47
    cG
    fveq2
    #
    oveq2d
    @72
    @26
    @59
    cF
    @74
    fveq2d
    oveq12d
    f1oeq123d
    imbi12d
    wph
    @36
    @44
    wph
    @36
    wa
    #
    vx
    vz
    cA
    cB
    cS
    cT
    vf
    vk
    cF
    cG
    cH
    c0
    cK
    cM
    c0
    cnfcom.s
    wph
    cA
    con0
    wcel
    #
    @36
    cnfcom.a
    adantr
    wph
    cB
    @19
    wcel
    #
    @36
    cnfcom.b
    adantr
    cnfcom.f
    cnfcom.g
    cnfcom.h
    cnfcom.t
    cnfcom.m
    cnfcom.k
    wph
    @36
    simpr
    @75
    @15
    @39
    con0
    wcel
    #
    c0
    com
    wcel
    #
    c0
    @40
    wcel
    @15
    @75
    omelon
    a1i
    wph
    @13
    con0
    wss
    @39
    @13
    wcel
    @78
    @36
    wph
    @13
    cA
    con0
    wph
    cF
    cdm
    #
    @13
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
    @80
    cA
    wceq
    wph
    @81
    cF
    c0
    cfsupp
    wbr
    #
    wph
    cF
    cS
    wcel
    @81
    @82
    wa
    @20
    wph
    com
    cA
    cS
    cF
    cnfcom.s
    @16
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
    #
    wph
    @76
    cA
    con0
    wss
    #
    cnfcom.a
    cA
    onss
    syl
    #
    sstrd
    @0
    @13
    c0
    cG
    @13
    cep
    cG
    cnfcom.g
    oif
    #
    ffvelrni
    @13
    con0
    @39
    ssel2
    syl2an
    @79
    @75
    peano1
    a1i
    com
    @39
    oen0
    syl21anc
    c0
    cT
    cfv
    #
    c0
    wceq
    #
    c0
    cH
    cfv
    #
    c0
    @88
    wf1o
    #
    @75
    c0
    cvv
    wcel
    #
    @89
    0ex
    vk
    vf
    cvv
    cvv
    cK
    cmpt2
    cT
    c0
    cvv
    cnfcom.t
    seqom0g
    ax-mp
    @89
    @91
    @90
    c0
    c0
    wf1o
    #
    @93
    c0
    c0
    c0
    wf1o
    #
    f1o0
    @92
    @90
    c0
    wceq
    @93
    @94
    wb
    0ex
    vk
    vz
    cvv
    cvv
    cM
    vz
    cv
    coa
    co
    cmpt2
    cH
    c0
    cvv
    cnfcom.h
    seqom0g
    @90
    c0
    c0
    c0
    f1oeq2
    mp2b
    mpbir
    @90
    c0
    @88
    c0
    f1oeq1
    mpbiri
    mp1i
    cnfcomlem
    ex
    wph
    @45
    com
    wcel
    #
    @55
    @65
    wi
    @55
    @56
    @54
    wi
    wph
    @95
    wa
    #
    @65
    @56
    @46
    @54
    @0
    wtr
    #
    @56
    @46
    @0
    word
    @97
    @13
    cep
    cG
    cnfcom.g
    oicl
    @0
    ordtr
    ax-mp
    @0
    @45
    trsuc
    mpan
    #
    imim1i
    @96
    @56
    @54
    @64
    @96
    @56
    @54
    @64
    @96
    @56
    @54
    wa
    #
    wa
    #
    vx
    vz
    cA
    cB
    cS
    cT
    vf
    vk
    cF
    cG
    cH
    @47
    cK
    cM
    @52
    cnfcom.s
    wph
    @76
    @95
    @99
    cnfcom.a
    ad2antrr
    wph
    @77
    @95
    @99
    cnfcom.b
    ad2antrr
    cnfcom.f
    cnfcom.g
    cnfcom.h
    cnfcom.t
    cnfcom.m
    cnfcom.k
    @96
    @56
    @54
    simprl
    #
    @100
    com
    @49
    csuc
    #
    coe
    co
    #
    @60
    @52
    @100
    @102
    @59
    wss
    #
    @103
    @60
    wss
    #
    @100
    @59
    word
    #
    @49
    @59
    wcel
    #
    @104
    @100
    @59
    con0
    wcel
    #
    @106
    @100
    cA
    con0
    @59
    wph
    @85
    @95
    @99
    @86
    ad2antrr
    #
    @100
    @13
    cA
    @59
    wph
    @13
    cA
    wss
    @95
    @99
    @84
    ad2antrr
    #
    @56
    @59
    @13
    wcel
    @96
    @54
    @0
    @13
    @47
    cG
    @87
    ffvelrni
    ad2antrl
    sseldd
    sseldd
    #
    @59
    eloni
    syl
    @100
    @45
    @47
    wcel
    #
    @107
    @45
    vy
    vex
    #
    sucid
    @100
    @45
    @47
    cep
    wbr
    #
    @49
    @59
    cep
    wbr
    #
    @112
    @107
    @100
    @0
    @13
    cep
    cep
    cG
    wiso
    #
    @46
    @56
    @114
    @115
    wb
    wph
    @116
    @95
    @99
    wph
    @13
    cvv
    wcel
    @14
    @116
    wph
    @13
    cA
    con0
    cnfcom.a
    @84
    ssexd
    wph
    @14
    @12
    @21
    simpld
    @13
    cep
    cG
    cvv
    cnfcom.g
    oiiso
    syl2anc
    ad2antrr
    @56
    @46
    @96
    @54
    @98
    ad2antrl
    #
    @101
    @0
    @13
    @45
    @47
    cep
    cep
    cG
    isorel
    syl12anc
    @45
    @47
    @45
    @113
    sucex
    epelc
    @49
    @59
    @47
    cG
    fvex
    epelc
    3bitr3g
    mpbii
    @49
    @59
    ordsucss
    sylc
    @100
    @102
    con0
    wcel
    #
    @108
    @15
    @79
    @104
    @105
    wi
    @100
    @49
    con0
    wcel
    #
    @118
    @100
    cA
    con0
    @49
    @109
    @100
    @13
    cA
    @49
    @110
    @100
    @46
    @49
    @13
    wcel
    @117
    @0
    @13
    @45
    cG
    @87
    ffvelrni
    syl
    sseldd
    #
    sseldd
    #
    @49
    suceloni
    syl
    @111
    @15
    @100
    omelon
    a1i
    #
    @79
    @100
    peano1
    a1i
    #
    @102
    @59
    com
    oewordi
    syl31anc
    mpd
    @100
    @52
    @50
    com
    comu
    co
    #
    @103
    @100
    @51
    com
    wcel
    #
    @52
    @124
    wcel
    #
    @100
    cA
    com
    @49
    cF
    wph
    @81
    @95
    @99
    @83
    ad2antrr
    @120
    ffvelrnd
    #
    @100
    @51
    con0
    wcel
    #
    @15
    @50
    con0
    wcel
    #
    c0
    @50
    wcel
    #
    @125
    @126
    wb
    @100
    @125
    @128
    @127
    @51
    nnon
    syl
    @122
    @100
    @15
    @119
    @129
    @122
    @121
    com
    @49
    oecl
    syl2anc
    @100
    @15
    @119
    @79
    @130
    @122
    @121
    @123
    com
    @49
    oen0
    syl21anc
    @51
    com
    @50
    omord2
    syl31anc
    mpbid
    @100
    @15
    @119
    @103
    @124
    wceq
    @122
    @121
    com
    @49
    oesuc
    syl2anc
    eleqtrrd
    sseldd
    @96
    @56
    @54
    simprr
    cnfcomlem
    exp32
    a2d
    syl5
    expcom
    finds2
    vtoclga
    mpcom
    mpd
end
