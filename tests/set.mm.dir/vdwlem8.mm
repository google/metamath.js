include "c1.mm"
include "cop.mm"
include "cvdwp.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "cvdwa.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "cfz.mm"
include "wral.mm"
include "cmpt.mm"
include "crn.mm"
include "chash.mm"
include "wceq.mm"
include "wa.mm"
include "cn.mm"
include "cmap.mm"
include "wrex.mm"
include "cmin.mm"
include "wcel.mm"
include "nncnd.mm"
include "addcomd.mm"
include "oveq2d.mm"
include "subsub4d.mm"
include "eqtr4d.mm"
include "subcld.mm"
include "ppncand.mm"
include "eqtrd.mm"
include "cn0.mm"
include "nnaddcld.mm"
include "cuz.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fvex.mm"
include "dmmpti.mm"
include "sseqtri.mm"
include "syl6ss.mm"
include "cun.mm"
include "ssun2.mm"
include "c2.mm"
include "uz2m1nn.mm"
include "syl.mm"
include "vdwapid1.mm"
include "syl3anc.mm"
include "sseldi.mm"
include "cc.mm"
include "eluz2nn.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "fveq2d.mm"
include "oveqd.mm"
include "nnnn0d.mm"
include "vdwapun.mm"
include "eqtr3d.mm"
include "eleqtrrd.mm"
include "sseldd.mm"
include "elfzuz3.mm"
include "uznn0sub.mm"
include "3syl.mm"
include "nnnn0addcl.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "wf.mm"
include "wf1o.mm"
include "1nn.mm"
include "f1osng.mm"
include "sylancr.mm"
include "f1of.mm"
include "snssd.mm"
include "fssd.mm"
include "cz.mm"
include "1z.mm"
include "fzsn.mm"
include "ax-mp.mm"
include "feq2i.mm"
include "sylibr.mm"
include "nnex.mm"
include "ovex.mm"
include "elmap.mm"
include "cmul.mm"
include "cc0.mm"
include "adantr.mm"
include "elfznn0.mm"
include "nn0mulcl.mm"
include "syl2anr.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "eqid.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan2.mm"
include "wb.mm"
include "vdwapval.mm"
include "biimpar.mm"
include "sylan2.mm"
include "wfn.mm"
include "fnmpti.mm"
include "fniniseg.mm"
include "sylib.mm"
include "simpld.mm"
include "eluzelz.mm"
include "eluzadd.mm"
include "mpdan.mm"
include "2timesd.mm"
include "nn0cnd.mm"
include "add32d.mm"
include "3eltr4d.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "fvmpt.mm"
include "simprd.mm"
include "3eqtr2d.mm"
include "jca.mm"
include "eleq1.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "ffn.mm"
include "3imtr4d.mm"
include "ssrdv.mm"
include "fvsng.mm"
include "addassd.mm"
include "npcand.mm"
include "3eqtrd.mm"
include "oveq12d.mm"
include "sneqd.mm"
include "imaeq2d.mm"
include "3sstr4d.mm"
include "ralrimivw.mm"
include "cxp.mm"
include "mpteq2dv.mm"
include "fconstmpt.mm"
include "syl6eqr.mm"
include "rneqd.mm"
include "c0.mm"
include "wne.mm"
include "elfz3.mm"
include "ne0i.mm"
include "mp2b.mm"
include "rnxp.mm"
include "syl6eq.mm"
include "cvv.mm"
include "hashsng.mm"
include "oveq1d.mm"
include "sseq12d.mm"
include "ralbidv.mm"
include "fveq1.mm"
include "elfz1eq.mm"
include "sylan9eq.mm"
include "ralbidva.mm"
include "mpteq2dva.mm"
include "rspc2ev.mm"
include "syl112anc.mm"
include "a1i.mm"
include "vdwpc.mm"
include "mpbird.mm"

theorem vdwlem8
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cD: class D
  let cR: class R
  let cF: class F
  let cG: class G
  let cK: class K
  let cW: class W
  let va: setvar a
  let vd: setvar d
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  assume vdwlem8.r: |- ( ph -> R e. Fin )
  assume vdwlem8.k: |- ( ph -> K e. ( ZZ>= ` 2 ) )
  assume vdwlem8.w: |- ( ph -> W e. NN )
  assume vdwlem8.f: |- ( ph -> F : ( 1 ... ( 2 x. W ) ) --> R )
  assume vdwlem8.c: |- C e. _V
  assume vdwlem8.a: |- ( ph -> A e. NN )
  assume vdwlem8.d: |- ( ph -> D e. NN )
  assume vdwlem8.s: |- ( ph -> ( A ( AP ` K ) D ) C_ ( `' G " { C } ) )
  assume vdwlem8.g: |- G = ( x e. ( 1 ... W ) |-> ( F ` ( x + W ) ) )

  disjoint A x
  disjoint D x
  disjoint F x
  disjoint ph x
  disjoint C x
  disjoint K x
  disjoint W x
  disjoint a d
  disjoint a i
  disjoint a m
  disjoint a n
  disjoint a x
  disjoint A a
  disjoint d i
  disjoint d m
  disjoint d n
  disjoint d x
  disjoint A d
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint A i
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint n x
  disjoint A n
  disjoint D a
  disjoint D d
  disjoint D i
  disjoint D m
  disjoint D n
  disjoint F a
  disjoint F d
  disjoint F i
  disjoint F m
  disjoint i ph
  disjoint m ph
  disjoint C i
  disjoint C m
  disjoint K a
  disjoint K d
  disjoint K i
  disjoint K m
  disjoint K n
  disjoint W a
  disjoint W d
  disjoint W i
  disjoint W m
  assert |- ( ph -> <. 1 , K >. PolyAP F )

  proof
    wph
    c1
    cK
    cop
    cF
    cvdwp
    wbr
    va
    cv
    #
    vi
    cv
    #
    vd
    cv
    #
    cfv
    #
    caddc
    co
    #
    @3
    cK
    cvdwa
    cfv
    #
    co
    #
    cF
    ccnv
    #
    @4
    cF
    cfv
    #
    csn
    #
    cima
    #
    wss
    #
    vi
    c1
    c1
    cfz
    co
    #
    wral
    #
    vi
    @12
    @8
    cmpt
    #
    crn
    #
    chash
    cfv
    #
    c1
    wceq
    #
    wa
    #
    vd
    cn
    @12
    cmap
    co
    #
    wrex
    va
    cn
    wrex
    #
    wph
    cA
    cW
    cD
    cmin
    co
    #
    caddc
    co
    #
    cn
    wcel
    c1
    cD
    cop
    csn
    #
    @19
    wcel
    #
    @22
    c1
    @23
    cfv
    #
    caddc
    co
    #
    @25
    @5
    co
    #
    @7
    @26
    cF
    cfv
    #
    csn
    #
    cima
    #
    wss
    #
    vi
    @12
    wral
    #
    vi
    @12
    @28
    cmpt
    #
    crn
    #
    chash
    cfv
    #
    c1
    wceq
    #
    @20
    wph
    cA
    cA
    caddc
    co
    #
    cW
    cA
    cD
    caddc
    co
    #
    cmin
    co
    #
    caddc
    co
    #
    @22
    cn
    wph
    @40
    @37
    @21
    cA
    cmin
    co
    #
    caddc
    co
    @22
    wph
    @39
    @41
    @37
    caddc
    wph
    @39
    cW
    cD
    cA
    caddc
    co
    #
    cmin
    co
    @41
    wph
    @38
    @42
    cW
    cmin
    wph
    cA
    cD
    wph
    cA
    vdwlem8.a
    nncnd
    #
    wph
    cD
    vdwlem8.d
    nncnd
    #
    addcomd
    oveq2d
    wph
    cW
    cD
    cA
    wph
    cW
    vdwlem8.w
    nncnd
    #
    @44
    @43
    subsub4d
    eqtr4d
    oveq2d
    wph
    cA
    cA
    @21
    @43
    @43
    wph
    cW
    cD
    @45
    @44
    subcld
    #
    ppncand
    eqtrd
    wph
    @37
    cn
    wcel
    @39
    cn0
    wcel
    #
    @40
    cn
    wcel
    wph
    cA
    cA
    vdwlem8.a
    vdwlem8.a
    nnaddcld
    wph
    @38
    c1
    cW
    cfz
    co
    #
    wcel
    cW
    @38
    cuz
    cfv
    wcel
    @47
    wph
    cA
    cD
    @5
    co
    #
    @48
    @38
    wph
    @49
    cG
    ccnv
    cC
    csn
    #
    cima
    #
    @48
    vdwlem8.s
    @51
    cG
    cdm
    @48
    cG
    @50
    cnvimass
    vx
    @48
    vx
    cv
    #
    cW
    caddc
    co
    #
    cF
    cfv
    #
    cG
    @53
    cF
    fvex
    #
    vdwlem8.g
    dmmpti
    sseqtri
    syl6ss
    wph
    @38
    cA
    csn
    #
    @38
    cD
    cK
    c1
    cmin
    co
    #
    cvdwa
    cfv
    co
    #
    cun
    #
    @49
    wph
    @58
    @59
    @38
    @58
    @56
    ssun2
    wph
    @57
    cn
    wcel
    #
    @38
    cn
    wcel
    cD
    cn
    wcel
    #
    @38
    @58
    wcel
    wph
    cK
    c2
    cuz
    cfv
    wcel
    #
    @60
    vdwlem8.k
    cK
    uz2m1nn
    syl
    #
    wph
    cA
    cD
    vdwlem8.a
    vdwlem8.d
    nnaddcld
    vdwlem8.d
    @38
    cD
    @57
    vdwapid1
    syl3anc
    sseldi
    wph
    cA
    cD
    @57
    c1
    caddc
    co
    #
    cvdwa
    cfv
    #
    co
    #
    @49
    @59
    wph
    @65
    @5
    cA
    cD
    wph
    @64
    cK
    cvdwa
    wph
    cK
    cc
    wcel
    c1
    cc
    wcel
    @64
    cK
    wceq
    wph
    cK
    wph
    @62
    cK
    cn
    wcel
    #
    vdwlem8.k
    cK
    eluz2nn
    syl
    #
    nncnd
    ax-1cn
    cK
    c1
    npcan
    sylancl
    fveq2d
    oveqd
    wph
    @57
    cn0
    wcel
    cA
    cn
    wcel
    #
    @61
    @66
    @59
    wceq
    wph
    @57
    @63
    nnnn0d
    vdwlem8.a
    vdwlem8.d
    cA
    cD
    @57
    vdwapun
    syl3anc
    eqtr3d
    eleqtrrd
    sseldd
    @38
    c1
    cW
    elfzuz3
    @38
    cW
    uznn0sub
    3syl
    @37
    @39
    nnnn0addcl
    syl2anc
    eqeltrrd
    wph
    @12
    cn
    @23
    wf
    #
    @24
    wph
    c1
    csn
    #
    cn
    @23
    wf
    @70
    wph
    @71
    cD
    csn
    #
    cn
    @23
    wph
    @71
    @72
    @23
    wf1o
    #
    @71
    @72
    @23
    wf
    wph
    c1
    cn
    wcel
    #
    @61
    @73
    1nn
    vdwlem8.d
    c1
    cD
    cn
    cn
    f1osng
    sylancr
    @71
    @72
    @23
    f1of
    syl
    wph
    cD
    cn
    vdwlem8.d
    snssd
    fssd
    @12
    @71
    cn
    @23
    c1
    cz
    wcel
    #
    @12
    @71
    wceq
    1z
    c1
    fzsn
    ax-mp
    feq2i
    sylibr
    cn
    @12
    @23
    nnex
    c1
    c1
    cfz
    ovex
    elmap
    sylibr
    wph
    @31
    vi
    @12
    wph
    cA
    cW
    caddc
    co
    #
    cD
    @5
    co
    #
    @7
    @50
    cima
    #
    @27
    @30
    wph
    vx
    @77
    @78
    wph
    @52
    @76
    vm
    cv
    #
    cD
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vm
    cc0
    @57
    cfz
    co
    #
    wrex
    #
    @52
    c1
    c2
    cW
    cmul
    co
    #
    cfz
    co
    #
    wcel
    #
    @52
    cF
    cfv
    #
    cC
    wceq
    #
    wa
    #
    @52
    @77
    wcel
    #
    @52
    @78
    wcel
    #
    wph
    @82
    @90
    vm
    @83
    wph
    @79
    @83
    wcel
    #
    wa
    #
    @90
    @82
    @81
    @86
    wcel
    #
    @81
    cF
    cfv
    #
    cC
    wceq
    #
    wa
    @94
    @95
    @97
    @94
    @81
    c1
    cuz
    cfv
    #
    wcel
    @85
    @81
    cuz
    cfv
    #
    wcel
    @95
    @94
    @81
    cn
    @98
    @94
    @76
    cn
    wcel
    #
    @80
    cn0
    wcel
    #
    @81
    cn
    wcel
    wph
    @100
    @93
    wph
    cA
    cW
    vdwlem8.a
    vdwlem8.w
    nnaddcld
    #
    adantr
    @93
    @79
    cn0
    wcel
    cD
    cn0
    wcel
    @101
    wph
    @79
    @57
    elfznn0
    wph
    cD
    vdwlem8.d
    nnnn0d
    @79
    cD
    nn0mulcl
    syl2anr
    #
    @76
    @80
    nnnn0addcl
    syl2anc
    nnuz
    syl6eleq
    @94
    cW
    cW
    caddc
    co
    #
    cA
    @80
    caddc
    co
    #
    cW
    caddc
    co
    #
    cuz
    cfv
    #
    @85
    @99
    @94
    @105
    @48
    wcel
    #
    cW
    @105
    cuz
    cfv
    wcel
    #
    @104
    @107
    wcel
    #
    @94
    @108
    @105
    cG
    cfv
    #
    cC
    wceq
    #
    @94
    @105
    @51
    wcel
    #
    @108
    @112
    wa
    #
    @94
    @49
    @51
    @105
    wph
    @49
    @51
    wss
    @93
    vdwlem8.s
    adantr
    @93
    wph
    @105
    cA
    vn
    cv
    #
    cD
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vn
    @83
    wrex
    #
    @105
    @49
    wcel
    #
    @93
    @105
    @105
    wceq
    #
    @119
    @105
    eqid
    @118
    @121
    vn
    @79
    @83
    @115
    @79
    wceq
    #
    @117
    @105
    @105
    @122
    @116
    @80
    cA
    caddc
    @115
    @79
    cD
    cmul
    oveq1
    oveq2d
    eqeq2d
    rspcev
    mpan2
    wph
    @120
    @119
    wph
    cK
    cn0
    wcel
    #
    @69
    @61
    @120
    @119
    wb
    wph
    cK
    @68
    nnnn0d
    #
    vdwlem8.a
    vdwlem8.d
    cA
    cD
    vn
    cK
    @105
    vdwapval
    syl3anc
    biimpar
    sylan2
    sseldd
    cG
    @48
    wfn
    #
    @113
    @114
    wb
    vx
    @48
    @54
    cG
    @55
    vdwlem8.g
    fnmpti
    #
    @48
    cC
    @105
    cG
    fniniseg
    ax-mp
    sylib
    #
    simpld
    #
    @105
    c1
    cW
    elfzuz3
    @109
    cW
    cz
    wcel
    @110
    @105
    cW
    eluzelz
    cW
    @105
    cW
    eluzadd
    mpdan
    3syl
    wph
    @85
    @104
    wceq
    @93
    wph
    cW
    @45
    2timesd
    adantr
    @94
    @81
    @106
    cuz
    @94
    cA
    cW
    @80
    wph
    cA
    cc
    wcel
    @93
    @43
    adantr
    wph
    cW
    cc
    wcel
    @93
    @45
    adantr
    @94
    @80
    @103
    nn0cnd
    add32d
    #
    fveq2d
    3eltr4d
    @81
    c1
    @85
    elfzuzb
    sylanbrc
    @94
    @96
    @106
    cF
    cfv
    #
    @111
    cC
    @94
    @81
    @106
    cF
    @129
    fveq2d
    @94
    @108
    @111
    @130
    wceq
    @128
    vx
    @105
    @54
    @130
    @48
    cG
    @52
    @105
    wceq
    @53
    @106
    cF
    @52
    @105
    cW
    caddc
    oveq1
    fveq2d
    vdwlem8.g
    @106
    cF
    fvex
    fvmpt
    syl
    @94
    @108
    @112
    @127
    simprd
    3eqtr2d
    jca
    @82
    @87
    @95
    @89
    @97
    @52
    @81
    @86
    eleq1
    @82
    @88
    @96
    cC
    @52
    @81
    cF
    fveq2
    eqeq1d
    anbi12d
    syl5ibrcom
    rexlimdva
    wph
    @123
    @100
    @61
    @91
    @84
    wb
    @124
    @102
    vdwlem8.d
    @76
    cD
    vm
    cK
    @52
    vdwapval
    syl3anc
    wph
    @86
    cR
    cF
    wf
    cF
    @86
    wfn
    @92
    @90
    wb
    vdwlem8.f
    @86
    cR
    cF
    ffn
    @86
    cC
    @52
    cF
    fniniseg
    3syl
    3imtr4d
    ssrdv
    wph
    @26
    @76
    @25
    cD
    @5
    wph
    @26
    @22
    cD
    caddc
    co
    cA
    @21
    cD
    caddc
    co
    #
    caddc
    co
    @76
    wph
    @25
    cD
    @22
    caddc
    wph
    @74
    @61
    @25
    cD
    wceq
    1nn
    vdwlem8.d
    c1
    cD
    cn
    cn
    fvsng
    sylancr
    #
    oveq2d
    wph
    cA
    @21
    cD
    @43
    @46
    @44
    addassd
    wph
    @131
    cW
    cA
    caddc
    wph
    cW
    cD
    @45
    @44
    npcand
    oveq2d
    3eqtrd
    #
    @132
    oveq12d
    wph
    @29
    @50
    @7
    wph
    @28
    cC
    wph
    @28
    @76
    cF
    cfv
    #
    cA
    cG
    cfv
    #
    cC
    wph
    @26
    @76
    cF
    @133
    fveq2d
    wph
    cA
    @48
    wcel
    #
    @135
    @134
    wceq
    wph
    @136
    @135
    cC
    wceq
    #
    wph
    cA
    @51
    wcel
    #
    @136
    @137
    wa
    #
    wph
    @49
    @51
    cA
    vdwlem8.s
    wph
    @67
    @69
    @61
    cA
    @49
    wcel
    @68
    vdwlem8.a
    vdwlem8.d
    cA
    cD
    cK
    vdwapid1
    syl3anc
    sseldd
    @125
    @138
    @139
    wb
    @126
    @48
    cC
    cA
    cG
    fniniseg
    ax-mp
    sylib
    #
    simpld
    vx
    cA
    @54
    @134
    @48
    cG
    @52
    cA
    wceq
    @53
    @76
    cF
    @52
    cA
    cW
    caddc
    oveq1
    fveq2d
    vdwlem8.g
    @76
    cF
    fvex
    fvmpt
    syl
    wph
    @136
    @137
    @140
    simprd
    3eqtr2d
    #
    sneqd
    imaeq2d
    3sstr4d
    ralrimivw
    wph
    @35
    @50
    chash
    cfv
    #
    c1
    wph
    @34
    @50
    chash
    wph
    @34
    @12
    @50
    cxp
    #
    crn
    #
    @50
    wph
    @33
    @143
    wph
    @33
    vi
    @12
    cC
    cmpt
    @143
    wph
    vi
    @12
    @28
    cC
    @141
    mpteq2dv
    vi
    @12
    cC
    fconstmpt
    syl6eqr
    rneqd
    @12
    c0
    wne
    #
    @144
    @50
    wceq
    @75
    c1
    @12
    wcel
    @145
    1z
    c1
    elfz3
    @12
    c1
    ne0i
    mp2b
    @12
    @50
    rnxp
    ax-mp
    syl6eq
    fveq2d
    cC
    cvv
    wcel
    @142
    c1
    wceq
    vdwlem8.c
    cC
    cvv
    hashsng
    ax-mp
    syl6eq
    @18
    @32
    @36
    wa
    @22
    @3
    caddc
    co
    #
    @3
    @5
    co
    #
    @7
    @146
    cF
    cfv
    #
    csn
    #
    cima
    #
    wss
    #
    vi
    @12
    wral
    #
    vi
    @12
    @148
    cmpt
    #
    crn
    #
    chash
    cfv
    #
    c1
    wceq
    #
    wa
    va
    vd
    @22
    @23
    cn
    @19
    @0
    @22
    wceq
    #
    @13
    @152
    @17
    @156
    @157
    @11
    @151
    vi
    @12
    @157
    @6
    @147
    @10
    @150
    @157
    @4
    @146
    @3
    @5
    @0
    @22
    @3
    caddc
    oveq1
    #
    oveq1d
    @157
    @9
    @149
    @7
    @157
    @8
    @148
    @157
    @4
    @146
    cF
    @158
    fveq2d
    #
    sneqd
    imaeq2d
    sseq12d
    ralbidv
    @157
    @16
    @155
    c1
    @157
    @15
    @154
    chash
    @157
    @14
    @153
    @157
    vi
    @12
    @8
    @148
    @159
    mpteq2dv
    rneqd
    fveq2d
    eqeq1d
    anbi12d
    @2
    @23
    wceq
    #
    @152
    @32
    @156
    @36
    @160
    @151
    @31
    vi
    @12
    @160
    @1
    @12
    wcel
    #
    wa
    #
    @147
    @27
    @150
    @30
    @162
    @146
    @26
    @3
    @25
    @5
    @162
    @3
    @25
    @22
    caddc
    @160
    @161
    @3
    @1
    @23
    cfv
    @25
    @1
    @2
    @23
    fveq1
    @161
    @1
    c1
    @23
    @1
    c1
    elfz1eq
    fveq2d
    sylan9eq
    #
    oveq2d
    #
    @163
    oveq12d
    @162
    @149
    @29
    @7
    @162
    @148
    @28
    @162
    @146
    @26
    cF
    @164
    fveq2d
    #
    sneqd
    imaeq2d
    sseq12d
    ralbidva
    @160
    @155
    @35
    c1
    @160
    @154
    @34
    chash
    @160
    @153
    @33
    @160
    vi
    @12
    @148
    @28
    @165
    mpteq2dva
    rneqd
    fveq2d
    eqeq1d
    anbi12d
    rspc2ev
    syl112anc
    wph
    cR
    vi
    cF
    @12
    cK
    c1
    @86
    va
    vd
    c1
    @85
    cfz
    ovex
    @124
    vdwlem8.f
    @74
    wph
    1nn
    a1i
    @12
    eqid
    vdwpc
    mpbird
end
