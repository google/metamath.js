include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "ccom.mm"
include "cseq.mm"
include "wf1o.mm"
include "wf.mm"
include "wceq.mm"
include "eqid.mm"
include "fmptd.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "cuz.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "wb.mm"
include "oveq2.mm"
include "f1oeq23.mm"
include "syl2anc.mm"
include "feq2d.mm"
include "anbi12d.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "2albidv.mm"
include "imbi2d.mm"
include "weq.mm"
include "cz.mm"
include "f1of.mm"
include "adantr.mm"
include "elfz3.mm"
include "fvco3.mm"
include "syl2anr.mm"
include "ffvelrn.mm"
include "csn.mm"
include "fzsn.mm"
include "eleq2d.mm"
include "elsni.mm"
include "syl6bi.mm"
include "imp.mm"
include "syldan.mm"
include "adantrr.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "seq1.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "alrimivv.mm"
include "a1d.mm"
include "f1oeq1.mm"
include "feq1.mm"
include "bi2anan9r.mm"
include "coeq1.mm"
include "coeq2.mm"
include "sylan9eq.mm"
include "seqeq3d.mm"
include "fveq1d.mm"
include "simpl.mm"
include "cbval2v.mm"
include "ccnv.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "simplll.mm"
include "sylan.mm"
include "w3a.mm"
include "simpllr.mm"
include "wss.mm"
include "syl.mm"
include "simprl.mm"
include "simprr.mm"
include "simplr.mm"
include "sylib.mm"
include "seqf1olem2.mm"
include "exp31.mm"
include "syl5bir.mm"
include "alrimdv.mm"
include "syl5bi.mm"
include "expcom.mm"
include "a2d.mm"
include "uzind4.mm"
include "mpcom.mm"
include "cfn.mm"
include "cvv.mm"
include "wfn.mm"
include "fvex.mm"
include "fnmpti.mm"
include "fzfi.mm"
include "fnfi.mm"
include "mp2an.mm"
include "ovexd.mm"
include "fex2.mm"
include "syl3anc.mm"
include "spc2gv.mm"
include "sylancr.mm"
include "mpd.mm"
include "mp2and.mm"
include "ffvelrnda.mm"
include "fvmpt.mm"
include "seqfveq.mm"
include "adantl.mm"
include "3eqtr3d.mm"

theorem seqf1o
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let c.pl: class .+
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let cJ: class J
  let cK: class K
  assume seqf1o.1: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x .+ y ) e. S )
  assume seqf1o.2: |- ( ( ph /\ ( x e. C /\ y e. C ) ) -> ( x .+ y ) = ( y .+ x ) )
  assume seqf1o.3: |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x .+ y ) .+ z ) = ( x .+ ( y .+ z ) ) )
  assume seqf1o.4: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume seqf1o.5: |- ( ph -> C C_ S )
  assume seqf1o.6: |- ( ph -> F : ( M ... N ) -1-1-onto-> ( M ... N ) )
  assume seqf1o.7: |- ( ( ph /\ x e. ( M ... N ) ) -> ( G ` x ) e. C )
  assume seqf1o.8: |- ( ( ph /\ k e. ( M ... N ) ) -> ( H ` k ) = ( G ` ( F ` k ) ) )

  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G k
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint M k
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint .+ k
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint N k
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint S k
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint C k
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint H k
  disjoint f g
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint g k
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint F g
  disjoint f m
  disjoint f n
  disjoint G f
  disjoint g m
  disjoint g n
  disjoint G g
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint G m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint G n
  disjoint f s
  disjoint f t
  disjoint f w
  disjoint M f
  disjoint g s
  disjoint g t
  disjoint g w
  disjoint M g
  disjoint k s
  disjoint k t
  disjoint k w
  disjoint m s
  disjoint m t
  disjoint m w
  disjoint M m
  disjoint n s
  disjoint n t
  disjoint n w
  disjoint M n
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint M s
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint M t
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint M w
  disjoint .+ f
  disjoint .+ g
  disjoint .+ m
  disjoint .+ n
  disjoint .+ s
  disjoint .+ t
  disjoint .+ w
  disjoint J f
  disjoint J g
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint N f
  disjoint N g
  disjoint N m
  disjoint N n
  disjoint K k
  disjoint K m
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint f ph
  disjoint g ph
  disjoint m ph
  disjoint n ph
  disjoint ph s
  disjoint ph t
  disjoint ph w
  disjoint S s
  disjoint S t
  disjoint S w
  disjoint C f
  disjoint C g
  disjoint C s
  disjoint C t
  disjoint C w
  assert |- ( ph -> ( seq M ( .+ , H ) ` N ) = ( seq M ( .+ , G ) ` N ) )

  proof
    wph
    cN
    c.pl
    vx
    cM
    cN
    cfz
    co
    #
    vx
    cv
    #
    cG
    cfv
    #
    cmpt
    #
    cF
    ccom
    #
    cM
    cseq
    #
    cfv
    #
    cN
    c.pl
    @3
    cM
    cseq
    #
    cfv
    #
    cN
    c.pl
    cH
    cM
    cseq
    cfv
    cN
    c.pl
    cG
    cM
    cseq
    cfv
    wph
    @0
    @0
    cF
    wf1o
    #
    @0
    cC
    @3
    wf
    #
    @6
    @8
    wceq
    #
    seqf1o.6
    wph
    vx
    @0
    @2
    cC
    @3
    seqf1o.7
    @3
    eqid
    #
    fmptd
    wph
    @0
    @0
    vf
    cv
    #
    wf1o
    #
    @0
    cC
    vg
    cv
    #
    wf
    #
    wa
    #
    cN
    c.pl
    @15
    @13
    ccom
    #
    cM
    cseq
    #
    cfv
    #
    cN
    c.pl
    @15
    cM
    cseq
    #
    cfv
    #
    wceq
    #
    wi
    #
    vf
    wal
    vg
    wal
    #
    @9
    @10
    wa
    #
    @11
    wi
    #
    cN
    cM
    cuz
    cfv
    #
    wcel
    wph
    @25
    seqf1o.4
    wph
    cM
    @1
    cfz
    co
    #
    @29
    @13
    wf1o
    #
    @29
    cC
    @15
    wf
    #
    wa
    #
    @1
    @19
    cfv
    #
    @1
    @21
    cfv
    #
    wceq
    #
    wi
    #
    vf
    wal
    vg
    wal
    #
    wi
    wph
    cM
    cM
    cfz
    co
    #
    @38
    @13
    wf1o
    #
    @38
    cC
    @15
    wf
    #
    wa
    #
    cM
    @19
    cfv
    #
    cM
    @21
    cfv
    #
    wceq
    #
    wi
    #
    vf
    wal
    vg
    wal
    #
    wi
    wph
    cM
    vk
    cv
    #
    cfz
    co
    #
    @48
    @13
    wf1o
    #
    @48
    cC
    @15
    wf
    #
    wa
    #
    @47
    @19
    cfv
    #
    @47
    @21
    cfv
    #
    wceq
    #
    wi
    #
    vf
    wal
    vg
    wal
    #
    wi
    wph
    cM
    @47
    c1
    caddc
    co
    #
    cfz
    co
    #
    @58
    @13
    wf1o
    #
    @58
    cC
    @15
    wf
    #
    wa
    #
    @57
    @19
    cfv
    #
    @57
    @21
    cfv
    #
    wceq
    #
    wi
    #
    vf
    wal
    #
    vg
    wal
    #
    wi
    wph
    @25
    wi
    vx
    vk
    cM
    cN
    @1
    cM
    wceq
    #
    @37
    @46
    wph
    @68
    @36
    @45
    vg
    vf
    @68
    @32
    @41
    @35
    @44
    @68
    @30
    @39
    @31
    @40
    @68
    @29
    @38
    wceq
    #
    @69
    @30
    @39
    wb
    @1
    cM
    cM
    cfz
    oveq2
    #
    @70
    @29
    @38
    @29
    @38
    @13
    f1oeq23
    syl2anc
    @68
    @29
    @38
    cC
    @15
    @70
    feq2d
    anbi12d
    @68
    @33
    @42
    @34
    @43
    @1
    cM
    @19
    fveq2
    @1
    cM
    @21
    fveq2
    eqeq12d
    imbi12d
    2albidv
    imbi2d
    vx
    vk
    weq
    #
    @37
    @56
    wph
    @71
    @36
    @55
    vg
    vf
    @71
    @32
    @51
    @35
    @54
    @71
    @30
    @49
    @31
    @50
    @71
    @29
    @48
    wceq
    #
    @72
    @30
    @49
    wb
    @1
    @47
    cM
    cfz
    oveq2
    #
    @73
    @29
    @48
    @29
    @48
    @13
    f1oeq23
    syl2anc
    @71
    @29
    @48
    cC
    @15
    @73
    feq2d
    anbi12d
    @71
    @33
    @52
    @34
    @53
    @1
    @47
    @19
    fveq2
    @1
    @47
    @21
    fveq2
    eqeq12d
    imbi12d
    2albidv
    imbi2d
    @1
    @57
    wceq
    #
    @37
    @67
    wph
    @74
    @36
    @65
    vg
    vf
    @74
    @32
    @61
    @35
    @64
    @74
    @30
    @59
    @31
    @60
    @74
    @29
    @58
    wceq
    #
    @75
    @30
    @59
    wb
    @1
    @57
    cM
    cfz
    oveq2
    #
    @76
    @29
    @58
    @29
    @58
    @13
    f1oeq23
    syl2anc
    @74
    @29
    @58
    cC
    @15
    @76
    feq2d
    anbi12d
    @74
    @33
    @62
    @34
    @63
    @1
    @57
    @19
    fveq2
    @1
    @57
    @21
    fveq2
    eqeq12d
    imbi12d
    2albidv
    imbi2d
    @1
    cN
    wceq
    #
    @37
    @25
    wph
    @77
    @36
    @24
    vg
    vf
    @77
    @32
    @17
    @35
    @23
    @77
    @30
    @14
    @31
    @16
    @77
    @29
    @0
    wceq
    #
    @78
    @30
    @14
    wb
    @1
    cN
    cM
    cfz
    oveq2
    #
    @79
    @29
    @0
    @29
    @0
    @13
    f1oeq23
    syl2anc
    @77
    @29
    @0
    cC
    @15
    @79
    feq2d
    anbi12d
    @77
    @33
    @20
    @34
    @22
    @1
    cN
    @19
    fveq2
    @1
    cN
    @21
    fveq2
    eqeq12d
    imbi12d
    2albidv
    imbi2d
    cM
    cz
    wcel
    #
    @46
    wph
    @80
    @45
    vg
    vf
    @80
    @41
    @44
    @80
    @41
    wa
    #
    cM
    @18
    cfv
    #
    cM
    @15
    cfv
    #
    @42
    @43
    @81
    @82
    cM
    @13
    cfv
    #
    @15
    cfv
    #
    @83
    @41
    @38
    @38
    @13
    wf
    #
    cM
    @38
    wcel
    #
    @82
    @85
    wceq
    @80
    @39
    @86
    @40
    @38
    @38
    @13
    f1of
    #
    adantr
    cM
    elfz3
    #
    @38
    @38
    cM
    @15
    @13
    fvco3
    syl2anr
    @81
    @84
    cM
    @15
    @80
    @39
    @84
    cM
    wceq
    #
    @40
    @80
    @39
    @84
    @38
    wcel
    #
    @90
    @39
    @86
    @87
    @91
    @80
    @88
    @89
    @38
    @38
    cM
    @13
    ffvelrn
    syl2anr
    @80
    @91
    @90
    @80
    @91
    @84
    cM
    csn
    #
    wcel
    @90
    @80
    @38
    @92
    @84
    cM
    fzsn
    eleq2d
    @84
    cM
    elsni
    syl6bi
    imp
    syldan
    adantrr
    fveq2d
    eqtrd
    @80
    @42
    @82
    wceq
    @41
    c.pl
    @18
    cM
    seq1
    adantr
    @80
    @43
    @83
    wceq
    @41
    c.pl
    @15
    cM
    seq1
    adantr
    3eqtr4d
    ex
    alrimivv
    a1d
    @47
    @28
    wcel
    #
    wph
    @56
    @67
    wph
    @93
    @56
    @67
    wi
    @56
    @48
    @48
    vt
    cv
    #
    wf1o
    #
    @48
    cC
    vs
    cv
    #
    wf
    #
    wa
    #
    @47
    c.pl
    @96
    @94
    ccom
    #
    cM
    cseq
    #
    cfv
    #
    @47
    c.pl
    @96
    cM
    cseq
    #
    cfv
    #
    wceq
    #
    wi
    #
    vt
    wal
    vs
    wal
    #
    wph
    @93
    wa
    #
    @67
    @55
    @105
    vg
    vf
    vs
    vt
    vg
    vs
    weq
    #
    vf
    vt
    weq
    #
    wa
    #
    @51
    @98
    @54
    @104
    @109
    @49
    @95
    @108
    @50
    @97
    @48
    @48
    @13
    @94
    f1oeq1
    @48
    cC
    @15
    @96
    feq1
    bi2anan9r
    @110
    @52
    @101
    @53
    @103
    @110
    @47
    @19
    @100
    @110
    @18
    @99
    c.pl
    cM
    @108
    @109
    @18
    @96
    @13
    ccom
    @99
    @15
    @96
    @13
    coeq1
    @13
    @94
    @96
    coeq2
    sylan9eq
    seqeq3d
    fveq1d
    @110
    @47
    @21
    @102
    @110
    @15
    @96
    c.pl
    cM
    @108
    @109
    simpl
    seqeq3d
    fveq1d
    eqeq12d
    imbi12d
    cbval2v
    #
    @107
    @106
    @66
    vg
    @107
    @106
    @65
    vf
    @106
    @56
    @107
    @65
    @111
    @107
    @56
    @61
    @64
    @107
    @56
    wa
    #
    @61
    wa
    #
    vx
    vy
    vz
    cC
    c.pl
    cS
    vt
    vs
    vw
    @13
    @15
    vw
    @48
    vw
    cv
    #
    @57
    @13
    ccnv
    cfv
    #
    clt
    wbr
    @114
    @114
    c1
    caddc
    co
    cif
    @13
    cfv
    cmpt
    #
    @115
    cM
    @47
    @113
    wph
    @1
    cS
    wcel
    #
    vy
    cv
    #
    cS
    wcel
    #
    wa
    @1
    @118
    c.pl
    co
    #
    cS
    wcel
    wph
    @93
    @56
    @61
    simplll
    #
    seqf1o.1
    sylan
    @113
    wph
    @1
    cC
    wcel
    @118
    cC
    wcel
    wa
    @120
    @118
    @1
    c.pl
    co
    wceq
    @121
    seqf1o.2
    sylan
    @113
    wph
    @117
    @119
    vz
    cv
    #
    cS
    wcel
    w3a
    @120
    @122
    c.pl
    co
    @1
    @118
    @122
    c.pl
    co
    c.pl
    co
    wceq
    @121
    seqf1o.3
    sylan
    wph
    @93
    @56
    @61
    simpllr
    @113
    wph
    cC
    cS
    wss
    @121
    seqf1o.5
    syl
    @112
    @59
    @60
    simprl
    @112
    @59
    @60
    simprr
    @116
    eqid
    @115
    eqid
    @113
    @56
    @106
    @107
    @56
    @61
    simplr
    @111
    sylib
    seqf1olem2
    exp31
    syl5bir
    alrimdv
    alrimdv
    syl5bi
    expcom
    a2d
    uzind4
    mpcom
    wph
    @3
    cfn
    wcel
    #
    cF
    cvv
    wcel
    #
    @25
    @27
    wi
    @3
    @0
    wfn
    @0
    cfn
    wcel
    @123
    vx
    @0
    @2
    @3
    @1
    cG
    fvex
    @12
    fnmpti
    cM
    cN
    fzfi
    @0
    @3
    fnfi
    mp2an
    wph
    @0
    @0
    cF
    wf
    #
    @0
    cvv
    wcel
    #
    @126
    @124
    wph
    @9
    @125
    seqf1o.6
    @0
    @0
    cF
    f1of
    syl
    #
    wph
    cM
    cN
    cfz
    ovexd
    #
    @128
    @0
    @0
    cF
    cvv
    cvv
    fex2
    syl3anc
    @24
    @27
    vg
    vf
    @3
    cF
    cfn
    cvv
    @15
    @3
    wceq
    #
    @13
    cF
    wceq
    #
    wa
    #
    @17
    @26
    @23
    @11
    @130
    @14
    @9
    @129
    @16
    @10
    @0
    @0
    @13
    cF
    f1oeq1
    @0
    cC
    @15
    @3
    feq1
    bi2anan9r
    @131
    @20
    @6
    @22
    @8
    @131
    cN
    @19
    @5
    @131
    @18
    @4
    c.pl
    cM
    @129
    @130
    @18
    @3
    @13
    ccom
    @4
    @15
    @3
    @13
    coeq1
    @13
    cF
    @3
    coeq2
    sylan9eq
    seqeq3d
    fveq1d
    @131
    cN
    @21
    @7
    @131
    @15
    @3
    c.pl
    cM
    @129
    @130
    simpl
    seqeq3d
    fveq1d
    eqeq12d
    imbi12d
    spc2gv
    sylancr
    mpd
    mp2and
    wph
    c.pl
    vk
    @4
    cH
    cM
    cN
    seqf1o.4
    wph
    @47
    @0
    wcel
    #
    wa
    #
    @47
    cF
    cfv
    #
    @3
    cfv
    #
    @134
    cG
    cfv
    #
    @47
    @4
    cfv
    #
    @47
    cH
    cfv
    @133
    @134
    @0
    wcel
    @135
    @136
    wceq
    wph
    @0
    @0
    @47
    cF
    @127
    ffvelrnda
    vx
    @134
    @2
    @136
    @0
    @3
    @1
    @134
    cG
    fveq2
    @12
    @134
    cG
    fvex
    fvmpt
    syl
    wph
    @125
    @132
    @137
    @135
    wceq
    @127
    @0
    @0
    @47
    @3
    cF
    fvco3
    sylan
    seqf1o.8
    3eqtr4d
    seqfveq
    wph
    c.pl
    vk
    @3
    cG
    cM
    cN
    seqf1o.4
    @132
    @47
    @3
    cfv
    @47
    cG
    cfv
    #
    wceq
    wph
    vx
    @47
    @2
    @138
    @0
    @3
    @1
    @47
    cG
    fveq2
    @12
    @47
    cG
    fvex
    fvmpt
    adantl
    seqfveq
    3eqtr3d
end
