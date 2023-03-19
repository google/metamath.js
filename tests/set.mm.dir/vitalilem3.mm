include "cv.mm"
include "cn.mm"
include "wcel.mm"
include "cfv.mm"
include "wa.mm"
include "wmo.mm"
include "wal.mm"
include "wdisj.mm"
include "weq.mm"
include "wi.mm"
include "wceq.mm"
include "cr.mm"
include "cmin.mm"
include "co.mm"
include "crn.mm"
include "crab.mm"
include "simprlr.mm"
include "simprll.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eleq1d.mm"
include "rabbidv.mm"
include "reex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "syl.mm"
include "eleqtrd.mm"
include "oveq1.mm"
include "elrab.mm"
include "sylib.mm"
include "simpld.mm"
include "recnd.mm"
include "cq.mm"
include "cc.mm"
include "wf.mm"
include "c1.mm"
include "cneg.mm"
include "cicc.mm"
include "cin.mm"
include "wss.mm"
include "wf1o.mm"
include "f1of.mm"
include "inss1.mm"
include "fss.mm"
include "sylancl.mm"
include "adantr.mm"
include "ffvelrnd.mm"
include "qcn.mm"
include "simprrl.mm"
include "cec.mm"
include "cc0.mm"
include "wer.mm"
include "vitalilem1.mm"
include "a1i.mm"
include "wbr.mm"
include "ciun.mm"
include "c2.mm"
include "vitalilem2.mm"
include "simp1d.mm"
include "simprd.mm"
include "sseldd.mm"
include "simprrr.mm"
include "jca.mm"
include "nnncan1d.mm"
include "qsubcl.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "oveq12.mm"
include "brab2a.mm"
include "sylanbrc.mm"
include "erthi.mm"
include "fveq2d.mm"
include "wral.mm"
include "eceq1d.mm"
include "eqeq12d.mm"
include "c0.mm"
include "wne.mm"
include "cqs.mm"
include "cvv.mm"
include "ovex.mm"
include "erex.mm"
include "mp2.mm"
include "ecelqsi.mm"
include "syl6eleqr.mm"
include "adantl.mm"
include "simpr.mm"
include "cdm.mm"
include "erdm.mm"
include "ax-mp.mm"
include "eleq2i.mm"
include "ecdmn0.mm"
include "bitr3i.mm"
include "neeq1.mm"
include "id.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "fvex.mm"
include "vex.mm"
include "elec.mm"
include "eqcomd.mm"
include "ectocld.mm"
include "ralrimiva.mm"
include "wfn.mm"
include "wb.mm"
include "eceq1.mm"
include "ralrn.mm"
include "mpbird.mm"
include "sylc.mm"
include "3eqtr3d.mm"
include "subcand.mm"
include "wf1.mm"
include "f1of1.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "mpbid.mm"
include "ex.mm"
include "alrimivv.mm"
include "eleq1.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "mo4.mm"
include "sylibr.mm"
include "alrimiv.mm"
include "dfdisj2.mm"

theorem vitalilem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.sm: class .~
  let cS: class S
  let cT: class T
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vs: setvar s
  let vk: setvar k
  let vv: setvar v
  let vw: setvar w
  let vu: setvar u
  assume vitali.1: |- .~ = { <. x , y >. | ( ( x e. ( 0 [,] 1 ) /\ y e. ( 0 [,] 1 ) ) /\ ( x - y ) e. QQ ) }
  assume vitali.2: |- S = ( ( 0 [,] 1 ) /. .~ )
  assume vitali.3: |- ( ph -> F Fn S )
  assume vitali.4: |- ( ph -> A. z e. S ( z =/= (/) -> ( F ` z ) e. z ) )
  assume vitali.5: |- ( ph -> G : NN -1-1-onto-> ( QQ i^i ( -u 1 [,] 1 ) ) )
  assume vitali.6: |- T = ( n e. NN |-> { s e. RR | ( s - ( G ` n ) ) e. ran F } )
  assume vitali.7: |- ( ph -> -. ran F e. ( ~P RR \ dom vol ) )

  disjoint m n
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint G m
  disjoint n s
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint G n
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint G s
  disjoint x y
  disjoint x z
  disjoint G x
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint ph z
  disjoint S z
  disjoint T m
  disjoint T x
  disjoint F m
  disjoint F n
  disjoint F s
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint .~ m
  disjoint .~ n
  disjoint .~ s
  disjoint .~ x
  disjoint .~ y
  disjoint .~ z
  disjoint k m
  disjoint k n
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k z
  disjoint k ph
  disjoint m v
  disjoint m w
  disjoint n v
  disjoint n w
  disjoint v w
  disjoint v x
  disjoint v z
  disjoint ph v
  disjoint w x
  disjoint w z
  disjoint ph w
  disjoint S w
  disjoint T k
  disjoint T v
  disjoint T w
  disjoint k s
  disjoint k y
  disjoint F k
  disjoint s v
  disjoint s w
  disjoint v y
  disjoint F v
  disjoint w y
  disjoint F w
  disjoint m u
  disjoint n u
  disjoint s u
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint .~ u
  disjoint .~ v
  disjoint .~ w
  assert |- ( ph -> Disj_ m e. NN ( T ` m ) )

  proof
    wph
    vm
    cv
    #
    cn
    wcel
    #
    vw
    cv
    #
    @0
    cT
    cfv
    #
    wcel
    #
    wa
    #
    vm
    wmo
    #
    vw
    wal
    vm
    cn
    @3
    wdisj
    wph
    @6
    vw
    wph
    @5
    vk
    cv
    #
    cn
    wcel
    #
    @2
    @7
    cT
    cfv
    #
    wcel
    #
    wa
    #
    wa
    #
    vm
    vk
    weq
    #
    wi
    #
    vk
    wal
    vm
    wal
    @6
    wph
    @14
    vm
    vk
    wph
    @12
    @13
    wph
    @12
    wa
    #
    @0
    cG
    cfv
    #
    @7
    cG
    cfv
    #
    wceq
    #
    @13
    @15
    @2
    @16
    @17
    @15
    @2
    @15
    @2
    cr
    wcel
    #
    @2
    @16
    cmin
    co
    #
    cF
    crn
    #
    wcel
    #
    @15
    @2
    vs
    cv
    #
    @16
    cmin
    co
    #
    @21
    wcel
    #
    vs
    cr
    crab
    #
    wcel
    @19
    @22
    wa
    @15
    @2
    @3
    @26
    wph
    @1
    @4
    @11
    simprlr
    @15
    @1
    @3
    @26
    wceq
    wph
    @1
    @4
    @11
    simprll
    #
    vn
    @0
    @23
    vn
    cv
    #
    cG
    cfv
    #
    cmin
    co
    #
    @21
    wcel
    #
    vs
    cr
    crab
    #
    @26
    cn
    cT
    vn
    vm
    weq
    #
    @31
    @25
    vs
    cr
    @33
    @30
    @24
    @21
    @33
    @29
    @16
    @23
    cmin
    @28
    @0
    cG
    fveq2
    oveq2d
    eleq1d
    rabbidv
    vitali.6
    @25
    vs
    cr
    reex
    rabex
    fvmpt
    syl
    eleqtrd
    @25
    @22
    vs
    @2
    cr
    vs
    vw
    weq
    #
    @24
    @20
    @21
    @23
    @2
    @16
    cmin
    oveq1
    eleq1d
    elrab
    sylib
    #
    simpld
    recnd
    #
    @15
    @16
    cq
    wcel
    #
    @16
    cc
    wcel
    @15
    cn
    cq
    @0
    cG
    wph
    cn
    cq
    cG
    wf
    #
    @12
    wph
    cn
    cq
    c1
    cneg
    #
    c1
    cicc
    co
    #
    cin
    #
    cG
    wf
    #
    @41
    cq
    wss
    @38
    wph
    cn
    @41
    cG
    wf1o
    #
    @42
    vitali.5
    cn
    @41
    cG
    f1of
    syl
    cq
    @40
    inss1
    cn
    @41
    cq
    cG
    fss
    sylancl
    adantr
    #
    @27
    ffvelrnd
    #
    @16
    qcn
    syl
    #
    @15
    @17
    cq
    wcel
    #
    @17
    cc
    wcel
    @15
    cn
    cq
    @7
    cG
    @44
    wph
    @5
    @8
    @10
    simprrl
    #
    ffvelrnd
    #
    @17
    qcn
    syl
    #
    @15
    @20
    c.sm
    cec
    #
    cF
    cfv
    #
    @2
    @17
    cmin
    co
    #
    c.sm
    cec
    #
    cF
    cfv
    #
    @20
    @53
    @15
    @51
    @54
    cF
    @15
    @20
    @53
    c.sm
    cc0
    c1
    cicc
    co
    #
    @56
    c.sm
    wer
    #
    @15
    vx
    vy
    c.sm
    vitali.1
    vitalilem1
    #
    a1i
    @15
    @20
    @56
    wcel
    #
    @53
    @56
    wcel
    #
    wa
    @20
    @53
    cmin
    co
    #
    cq
    wcel
    #
    @20
    @53
    c.sm
    wbr
    @15
    @59
    @60
    @15
    @21
    @56
    @20
    wph
    @21
    @56
    wss
    #
    @12
    wph
    @63
    @56
    vm
    cn
    @3
    ciun
    #
    wss
    @64
    @39
    c2
    cicc
    co
    wss
    wph
    vx
    vy
    vz
    c.sm
    cS
    cT
    vm
    vn
    cF
    cG
    vs
    vitali.1
    vitali.2
    vitali.3
    vitali.4
    vitali.5
    vitali.6
    vitali.7
    vitalilem2
    simp1d
    adantr
    #
    @15
    @19
    @22
    @35
    simprd
    #
    sseldd
    @15
    @21
    @56
    @53
    @65
    @15
    @19
    @53
    @21
    wcel
    #
    @15
    @2
    @23
    @17
    cmin
    co
    #
    @21
    wcel
    #
    vs
    cr
    crab
    #
    wcel
    @19
    @67
    wa
    @15
    @2
    @9
    @70
    wph
    @5
    @8
    @10
    simprrr
    @15
    @8
    @9
    @70
    wceq
    @48
    vn
    @7
    @32
    @70
    cn
    cT
    vn
    vk
    weq
    #
    @31
    @69
    vs
    cr
    @71
    @30
    @68
    @21
    @71
    @29
    @17
    @23
    cmin
    @28
    @7
    cG
    fveq2
    oveq2d
    eleq1d
    rabbidv
    vitali.6
    @69
    vs
    cr
    reex
    rabex
    fvmpt
    syl
    eleqtrd
    @69
    @67
    vs
    @2
    cr
    @34
    @68
    @53
    @21
    @23
    @2
    @17
    cmin
    oveq1
    eleq1d
    elrab
    sylib
    simprd
    #
    sseldd
    jca
    @15
    @61
    @17
    @16
    cmin
    co
    #
    cq
    @15
    @2
    @16
    @17
    @36
    @46
    @50
    nnncan1d
    @15
    @47
    @37
    @73
    cq
    wcel
    @49
    @45
    @17
    @16
    qsubcl
    syl2anc
    eqeltrd
    vx
    cv
    #
    vy
    cv
    #
    cmin
    co
    #
    cq
    wcel
    @62
    vx
    vy
    @20
    @53
    @56
    @56
    c.sm
    @74
    @20
    wceq
    @75
    @53
    wceq
    wa
    @76
    @61
    cq
    @74
    @20
    @75
    @53
    cmin
    oveq12
    eleq1d
    vitali.1
    brab2a
    sylanbrc
    erthi
    fveq2d
    @15
    @22
    vz
    cv
    #
    c.sm
    cec
    #
    cF
    cfv
    #
    @77
    wceq
    #
    vz
    @21
    wral
    #
    @52
    @20
    wceq
    #
    @66
    wph
    @81
    @12
    wph
    @81
    @2
    cF
    cfv
    #
    c.sm
    cec
    #
    cF
    cfv
    #
    @83
    wceq
    #
    vw
    cS
    wral
    #
    wph
    @86
    vw
    cS
    vv
    cv
    #
    c.sm
    cec
    #
    cF
    cfv
    #
    c.sm
    cec
    #
    cF
    cfv
    #
    @90
    wceq
    @86
    wph
    vv
    @2
    @56
    c.sm
    cS
    vitali.2
    @89
    @2
    wceq
    #
    @92
    @85
    @90
    @83
    @93
    @91
    @84
    cF
    @93
    @90
    @83
    c.sm
    @89
    @2
    cF
    fveq2
    #
    eceq1d
    fveq2d
    @94
    eqeq12d
    wph
    @88
    @56
    wcel
    #
    wa
    #
    @91
    @89
    cF
    @96
    @89
    @91
    @96
    @88
    @90
    c.sm
    @56
    @57
    @96
    @58
    a1i
    @96
    @90
    @89
    wcel
    #
    @88
    @90
    c.sm
    wbr
    @96
    @89
    cS
    wcel
    #
    @77
    c0
    wne
    #
    @77
    cF
    cfv
    #
    @77
    wcel
    #
    wi
    #
    vz
    cS
    wral
    #
    @89
    c0
    wne
    #
    @97
    @95
    @98
    wph
    @95
    @89
    @56
    c.sm
    cqs
    cS
    @56
    @88
    c.sm
    @57
    @56
    cvv
    wcel
    c.sm
    cvv
    wcel
    @58
    cc0
    c1
    cicc
    ovex
    @56
    c.sm
    cvv
    erex
    mp2
    ecelqsi
    vitali.2
    syl6eleqr
    adantl
    wph
    @103
    @95
    vitali.4
    adantr
    @96
    @95
    @104
    wph
    @95
    simpr
    @95
    @88
    c.sm
    cdm
    #
    wcel
    @104
    @105
    @56
    @88
    @57
    @105
    @56
    wceq
    @58
    @56
    c.sm
    erdm
    ax-mp
    eleq2i
    @88
    c.sm
    ecdmn0
    bitr3i
    sylib
    @102
    @104
    @97
    wi
    vz
    @89
    cS
    @77
    @89
    wceq
    #
    @99
    @104
    @101
    @97
    @77
    @89
    c0
    neeq1
    @106
    @100
    @90
    @77
    @89
    @77
    @89
    cF
    fveq2
    @106
    id
    eleq12d
    imbi12d
    rspcv
    syl3c
    @90
    @88
    c.sm
    @89
    cF
    fvex
    vv
    vex
    elec
    sylib
    erthi
    eqcomd
    fveq2d
    ectocld
    ralrimiva
    wph
    cF
    cS
    wfn
    @81
    @87
    wb
    vitali.3
    @80
    @86
    vz
    vw
    cS
    cF
    @77
    @83
    wceq
    #
    @79
    @85
    @77
    @83
    @107
    @78
    @84
    cF
    @77
    @83
    c.sm
    eceq1
    fveq2d
    @107
    id
    eqeq12d
    ralrn
    syl
    mpbird
    adantr
    #
    @80
    @82
    vz
    @20
    @21
    @77
    @20
    wceq
    #
    @79
    @52
    @77
    @20
    @109
    @78
    @51
    cF
    @77
    @20
    c.sm
    eceq1
    fveq2d
    @109
    id
    eqeq12d
    rspcv
    sylc
    @15
    @67
    @81
    @55
    @53
    wceq
    #
    @72
    @108
    @80
    @110
    vz
    @53
    @21
    @77
    @53
    wceq
    #
    @79
    @55
    @77
    @53
    @111
    @78
    @54
    cF
    @77
    @53
    c.sm
    eceq1
    fveq2d
    @111
    id
    eqeq12d
    rspcv
    sylc
    3eqtr3d
    subcand
    @15
    cn
    @41
    cG
    wf1
    #
    @1
    @8
    @18
    @13
    wb
    @15
    @43
    @112
    wph
    @43
    @12
    vitali.5
    adantr
    cn
    @41
    cG
    f1of1
    syl
    @27
    @48
    cn
    @41
    @0
    @7
    cG
    f1fveq
    syl12anc
    mpbid
    ex
    alrimivv
    @5
    @11
    vm
    vk
    @13
    @1
    @8
    @4
    @10
    @0
    @7
    cn
    eleq1
    @13
    @3
    @9
    @2
    @0
    @7
    cT
    fveq2
    eleq2d
    anbi12d
    mo4
    sylibr
    alrimiv
    vm
    vw
    cn
    @3
    dfdisj2
    sylibr
end
