include "crn.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "wss.mm"
include "cn.mm"
include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "cneg.mm"
include "c2.mm"
include "wf.mm"
include "wfn.mm"
include "wcel.mm"
include "wral.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "wa.mm"
include "cec.mm"
include "neeq1.mm"
include "cdm.mm"
include "wer.mm"
include "wceq.mm"
include "vitalilem1.mm"
include "erdm.mm"
include "ax-mp.mm"
include "eleq2i.mm"
include "ecdmn0.mm"
include "bitr3i.mm"
include "biimpi.mm"
include "ectocl.mm"
include "adantl.mm"
include "sseq1.mm"
include "a1i.mm"
include "ecss.mm"
include "sseld.mm"
include "embantd.mm"
include "ralimdva.mm"
include "mpd.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "frn.mm"
include "syl.mm"
include "cmin.mm"
include "ccnv.mm"
include "cq.mm"
include "cin.mm"
include "wf1o.mm"
include "adantr.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "3syl.mm"
include "cqs.mm"
include "cvv.mm"
include "ovex.mm"
include "erex.mm"
include "mp2.mm"
include "ecelqsi.mm"
include "syl6eleqr.mm"
include "simpr.mm"
include "sylib.mm"
include "fveq2.mm"
include "id.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "wbr.mm"
include "fvex.mm"
include "vex.mm"
include "elec.mm"
include "weq.mm"
include "oveq12.mm"
include "eleq1d.mm"
include "brab2a.mm"
include "bitri.mm"
include "simprd.mm"
include "cr.mm"
include "cle.mm"
include "w3a.mm"
include "0re.mm"
include "1re.mm"
include "elicc2i.mm"
include "simp1d.mm"
include "simpld.mm"
include "resubcld.mm"
include "1red.mm"
include "simp2d.mm"
include "subge02d.mm"
include "mpbid.mm"
include "simp3d.mm"
include "letrd.mm"
include "lenegd.mm"
include "recnd.mm"
include "negsubdi2d.mm"
include "breqtrd.mm"
include "neg1rr.mm"
include "syl3anbrc.mm"
include "elind.mm"
include "ffvelrnd.mm"
include "crab.mm"
include "f1ocnvfv2.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "nncand.mm"
include "eqtrd.mm"
include "fnfvelrn.mm"
include "eqeltrd.mm"
include "oveq1.mm"
include "elrab.mm"
include "rabbidv.mm"
include "reex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "eleqtrrd.mm"
include "jca.mm"
include "eliuni.mm"
include "ex.mm"
include "ssrdv.mm"
include "wrex.mm"
include "eliun.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "iccssre.mm"
include "mp2an.mm"
include "inss2.mm"
include "ffvelrnda.mm"
include "sseldi.mm"
include "ad2antrr.mm"
include "sseldd.mm"
include "subge0d.mm"
include "caddc.mm"
include "peano2re.mm"
include "2re.mm"
include "lesubadd2d.mm"
include "leadd1dd.mm"
include "df-2.mm"
include "syl6breqr.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "3jca.mm"

theorem vitalilem2
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
  assert |- ( ph -> ( ran F C_ ( 0 [,] 1 ) /\ ( 0 [,] 1 ) C_ U_ m e. NN ( T ` m ) /\ U_ m e. NN ( T ` m ) C_ ( -u 1 [,] 2 ) ) )

  proof
    wph
    cF
    crn
    #
    cc0
    c1
    cicc
    co
    #
    wss
    #
    @1
    vm
    cn
    vm
    cv
    #
    cT
    cfv
    #
    ciun
    #
    wss
    @5
    c1
    cneg
    #
    c2
    cicc
    co
    #
    wss
    wph
    cS
    @1
    cF
    wf
    #
    @2
    wph
    cF
    cS
    wfn
    #
    vz
    cv
    #
    cF
    cfv
    #
    @1
    wcel
    #
    vz
    cS
    wral
    #
    @8
    vitali.3
    wph
    @10
    c0
    wne
    #
    @11
    @10
    wcel
    #
    wi
    #
    vz
    cS
    wral
    #
    @13
    vitali.4
    wph
    @16
    @12
    vz
    cS
    wph
    @10
    cS
    wcel
    #
    wa
    #
    @14
    @15
    @12
    @18
    @14
    wph
    vv
    cv
    #
    c.sm
    cec
    #
    c0
    wne
    #
    @14
    vv
    @10
    @1
    c.sm
    cS
    vitali.2
    @21
    @10
    c0
    neeq1
    @20
    @1
    wcel
    #
    @22
    @23
    @20
    c.sm
    cdm
    #
    wcel
    @22
    @24
    @1
    @20
    @1
    c.sm
    wer
    #
    @24
    @1
    wceq
    vx
    vy
    c.sm
    vitali.1
    vitalilem1
    #
    @1
    c.sm
    erdm
    ax-mp
    eleq2i
    @20
    c.sm
    ecdmn0
    bitr3i
    #
    biimpi
    ectocl
    adantl
    @19
    @10
    @1
    @11
    @18
    @10
    @1
    wss
    #
    wph
    vw
    cv
    #
    c.sm
    cec
    #
    @1
    wss
    @28
    vw
    @10
    @1
    c.sm
    cS
    vitali.2
    @30
    @10
    @1
    sseq1
    @29
    @1
    wcel
    #
    @29
    c.sm
    @1
    @25
    @31
    @26
    a1i
    ecss
    ectocl
    adantl
    sseld
    embantd
    ralimdva
    mpd
    vz
    cS
    @1
    cF
    ffnfv
    sylanbrc
    cS
    @1
    cF
    frn
    syl
    #
    wph
    vv
    @1
    @5
    wph
    @23
    @20
    @5
    wcel
    #
    wph
    @23
    wa
    #
    @20
    @21
    cF
    cfv
    #
    cmin
    co
    #
    cG
    ccnv
    #
    cfv
    #
    cn
    wcel
    #
    @20
    @38
    cT
    cfv
    #
    wcel
    #
    wa
    @33
    @34
    @39
    @41
    @34
    cq
    @6
    c1
    cicc
    co
    #
    cin
    #
    cn
    @36
    @37
    @34
    cn
    @43
    cG
    wf1o
    #
    @43
    cn
    @37
    wf1o
    @43
    cn
    @37
    wf
    wph
    @44
    @23
    vitali.5
    adantr
    #
    cn
    @43
    cG
    f1ocnv
    @43
    cn
    @37
    f1of
    3syl
    @34
    cq
    @42
    @36
    @34
    @23
    @35
    @1
    wcel
    #
    wa
    #
    @36
    cq
    wcel
    #
    @34
    @35
    @21
    wcel
    #
    @47
    @48
    wa
    #
    @34
    @21
    cS
    wcel
    #
    @17
    @22
    @49
    @34
    @21
    @1
    c.sm
    cqs
    #
    cS
    @23
    @21
    @52
    wcel
    wph
    @1
    @20
    c.sm
    @25
    @1
    cvv
    wcel
    c.sm
    cvv
    wcel
    @26
    cc0
    c1
    cicc
    ovex
    @1
    c.sm
    cvv
    erex
    mp2
    ecelqsi
    adantl
    vitali.2
    syl6eleqr
    #
    wph
    @17
    @23
    vitali.4
    adantr
    @34
    @23
    @22
    wph
    @23
    simpr
    #
    @27
    sylib
    @16
    @22
    @49
    wi
    vz
    @21
    cS
    @10
    @21
    wceq
    #
    @14
    @22
    @15
    @49
    @10
    @21
    c0
    neeq1
    @55
    @11
    @35
    @10
    @21
    @10
    @21
    cF
    fveq2
    @55
    id
    eleq12d
    imbi12d
    rspcv
    syl3c
    @49
    @20
    @35
    c.sm
    wbr
    @50
    @35
    @20
    c.sm
    @21
    cF
    fvex
    vv
    vex
    elec
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
    @48
    vx
    vy
    @20
    @35
    @1
    @1
    c.sm
    vx
    vv
    weq
    @57
    @35
    wceq
    wa
    @58
    @36
    cq
    @56
    @20
    @57
    @35
    cmin
    oveq12
    eleq1d
    vitali.1
    brab2a
    bitri
    sylib
    #
    simprd
    @34
    @36
    cr
    wcel
    @6
    @36
    cle
    wbr
    @36
    c1
    cle
    wbr
    @36
    @42
    wcel
    @34
    @20
    @35
    @34
    @20
    cr
    wcel
    #
    cc0
    @20
    cle
    wbr
    #
    @20
    c1
    cle
    wbr
    #
    @34
    @23
    @60
    @61
    @62
    w3a
    @54
    cc0
    c1
    @20
    0re
    1re
    elicc2i
    sylib
    #
    simp1d
    #
    @34
    @35
    cr
    wcel
    #
    cc0
    @35
    cle
    wbr
    #
    @35
    c1
    cle
    wbr
    #
    @34
    @46
    @65
    @66
    @67
    w3a
    @34
    @23
    @46
    @34
    @47
    @48
    @59
    simpld
    simprd
    cc0
    c1
    @35
    0re
    1re
    elicc2i
    sylib
    #
    simp1d
    #
    resubcld
    #
    @34
    @6
    @35
    @20
    cmin
    co
    #
    cneg
    #
    @36
    cle
    @34
    @71
    c1
    cle
    wbr
    @6
    @72
    cle
    wbr
    @34
    @71
    @35
    c1
    @34
    @35
    @20
    @69
    @64
    resubcld
    #
    @69
    @34
    1red
    #
    @34
    @61
    @71
    @35
    cle
    wbr
    @34
    @60
    @61
    @62
    @63
    simp2d
    @34
    @35
    @20
    @69
    @64
    subge02d
    mpbid
    @34
    @65
    @66
    @67
    @68
    simp3d
    letrd
    @34
    @71
    c1
    @73
    @74
    lenegd
    mpbid
    @34
    @35
    @20
    @34
    @35
    @69
    recnd
    #
    @34
    @20
    @64
    recnd
    #
    negsubdi2d
    breqtrd
    @34
    @36
    @20
    c1
    @70
    @64
    @74
    @34
    @66
    @36
    @20
    cle
    wbr
    @34
    @65
    @66
    @67
    @68
    simp2d
    @34
    @20
    @35
    @64
    @69
    subge02d
    mpbid
    @34
    @60
    @61
    @62
    @63
    simp3d
    letrd
    @6
    c1
    @36
    neg1rr
    1re
    elicc2i
    syl3anbrc
    elind
    #
    ffvelrnd
    #
    @34
    @20
    vs
    cv
    #
    @38
    cG
    cfv
    #
    cmin
    co
    #
    @0
    wcel
    #
    vs
    cr
    crab
    #
    @40
    @34
    @60
    @20
    @80
    cmin
    co
    #
    @0
    wcel
    #
    @20
    @83
    wcel
    @64
    @34
    @84
    @35
    @0
    @34
    @84
    @20
    @36
    cmin
    co
    @35
    @34
    @80
    @36
    @20
    cmin
    @34
    @44
    @36
    @43
    wcel
    @80
    @36
    wceq
    @45
    @77
    cn
    @43
    @36
    cG
    f1ocnvfv2
    syl2anc
    oveq2d
    @34
    @20
    @35
    @76
    @75
    nncand
    eqtrd
    @34
    @9
    @51
    @35
    @0
    wcel
    wph
    @9
    @23
    vitali.3
    adantr
    @53
    cS
    @21
    cF
    fnfvelrn
    syl2anc
    eqeltrd
    @82
    @85
    vs
    @20
    cr
    vs
    vv
    weq
    @81
    @84
    @0
    @79
    @20
    @80
    cmin
    oveq1
    eleq1d
    elrab
    sylanbrc
    @34
    @39
    @40
    @83
    wceq
    @78
    vn
    @38
    @79
    vn
    cv
    #
    cG
    cfv
    #
    cmin
    co
    #
    @0
    wcel
    #
    vs
    cr
    crab
    #
    @83
    cn
    cT
    @86
    @38
    wceq
    #
    @89
    @82
    vs
    cr
    @91
    @88
    @81
    @0
    @91
    @87
    @80
    @79
    cmin
    @86
    @38
    cG
    fveq2
    oveq2d
    eleq1d
    rabbidv
    vitali.6
    @82
    vs
    cr
    reex
    rabex
    fvmpt
    syl
    eleqtrrd
    jca
    vm
    @38
    @4
    @40
    cn
    @20
    @3
    @38
    cT
    fveq2
    eliuni
    syl
    ex
    ssrdv
    wph
    vx
    @5
    @7
    @56
    @5
    wcel
    @56
    @4
    wcel
    #
    vm
    cn
    wrex
    wph
    @56
    @7
    wcel
    #
    vm
    @56
    cn
    @4
    eliun
    wph
    @92
    @93
    vm
    cn
    wph
    @3
    cn
    wcel
    #
    wa
    #
    @92
    @93
    @95
    @92
    wa
    #
    @56
    cr
    wcel
    #
    @6
    @56
    cle
    wbr
    @56
    c2
    cle
    wbr
    @93
    @96
    @97
    @56
    @3
    cG
    cfv
    #
    cmin
    co
    #
    @0
    wcel
    #
    @96
    @56
    @79
    @98
    cmin
    co
    #
    @0
    wcel
    #
    vs
    cr
    crab
    #
    wcel
    #
    @97
    @100
    wa
    @95
    @92
    @104
    @95
    @4
    @103
    @56
    @94
    @4
    @103
    wceq
    wph
    vn
    @3
    @90
    @103
    cn
    cT
    vn
    vm
    weq
    #
    @89
    @102
    vs
    cr
    @105
    @88
    @101
    @0
    @105
    @87
    @98
    @79
    cmin
    @86
    @3
    cG
    fveq2
    oveq2d
    eleq1d
    rabbidv
    vitali.6
    @102
    vs
    cr
    reex
    rabex
    fvmpt
    adantl
    eleq2d
    biimpa
    @102
    @100
    vs
    @56
    cr
    vs
    vx
    weq
    @101
    @99
    @0
    @79
    @56
    @98
    cmin
    oveq1
    eleq1d
    elrab
    sylib
    #
    simpld
    #
    @96
    @6
    @98
    @56
    @6
    cr
    wcel
    #
    @96
    neg1rr
    a1i
    @95
    @98
    cr
    wcel
    #
    @92
    @95
    @42
    cr
    @98
    @108
    c1
    cr
    wcel
    @42
    cr
    wss
    neg1rr
    1re
    @6
    c1
    iccssre
    mp2an
    @95
    @43
    @42
    @98
    cq
    @42
    inss2
    wph
    cn
    @43
    @3
    cG
    wph
    @44
    cn
    @43
    cG
    wf
    vitali.5
    cn
    @43
    cG
    f1of
    syl
    ffvelrnda
    sseldi
    #
    sseldi
    adantr
    #
    @107
    @96
    @109
    @6
    @98
    cle
    wbr
    #
    @98
    c1
    cle
    wbr
    #
    @96
    @98
    @42
    wcel
    #
    @109
    @112
    @113
    w3a
    @95
    @114
    @92
    @110
    adantr
    @6
    c1
    @98
    neg1rr
    1re
    elicc2i
    sylib
    #
    simp2d
    @96
    cc0
    @99
    cle
    wbr
    #
    @98
    @56
    cle
    wbr
    @96
    @99
    cr
    wcel
    #
    @116
    @99
    c1
    cle
    wbr
    #
    @96
    @99
    @1
    wcel
    @117
    @116
    @118
    w3a
    @96
    @0
    @1
    @99
    wph
    @2
    @94
    @92
    @32
    ad2antrr
    @96
    @97
    @100
    @106
    simprd
    sseldd
    cc0
    c1
    @99
    0re
    1re
    elicc2i
    sylib
    #
    simp2d
    @96
    @56
    @98
    @107
    @111
    subge0d
    mpbid
    letrd
    @96
    @56
    @98
    c1
    caddc
    co
    #
    c2
    @107
    @96
    @109
    @120
    cr
    wcel
    @111
    @98
    peano2re
    syl
    c2
    cr
    wcel
    @96
    2re
    a1i
    @96
    @118
    @56
    @120
    cle
    wbr
    @96
    @117
    @116
    @118
    @119
    simp3d
    @96
    @56
    @98
    c1
    @107
    @111
    @96
    1red
    #
    lesubadd2d
    mpbid
    @96
    @120
    c1
    c1
    caddc
    co
    c2
    cle
    @96
    @98
    c1
    c1
    @111
    @121
    @121
    @96
    @109
    @112
    @113
    @115
    simp3d
    leadd1dd
    df-2
    syl6breqr
    letrd
    @6
    c2
    @56
    neg1rr
    2re
    elicc2i
    syl3anbrc
    ex
    rexlimdva
    syl5bi
    ssrdv
    3jca
end
