include "cv.mm"
include "cfv.mm"
include "cneg.mm"
include "cmpt.mm"
include "crn.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "csmblfn.mm"
include "cinf.mm"
include "wceq.mm"
include "a1i.mm"
include "wcel.mm"
include "wa.mm"
include "nfv.mm"
include "c0.mm"
include "wne.mm"
include "uzn0d.mm"
include "adantr.mm"
include "cdm.mm"
include "wf.mm"
include "csalg.mm"
include "ffvelrnda.mm"
include "eqid.mm"
include "smff.mm"
include "adantlr.mm"
include "ciin.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "crab.mm"
include "ssrab2.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "sseldi.mm"
include "simpr.mm"
include "eliinid.mm"
include "syl2anc.mm"
include "adantll.mm"
include "ffvelrnd.mm"
include "rabidim2.mm"
include "syl.mm"
include "adantl.mm"
include "infnsuprnmpt.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "cvv.mm"
include "fvex.mm"
include "dmex.mm"
include "rgenw.mm"
include "iinexd.mm"
include "rabexd.mm"
include "renegcld.mm"
include "fveq2.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "rexbidv.mm"
include "nfcv.mm"
include "nfdm.mm"
include "nfiin.mm"
include "dmeqd.mm"
include "cbviin.mm"
include "wb.mm"
include "nffv.mm"
include "nfbr.mm"
include "fveq1d.mm"
include "cbvral.mm"
include "bitrd.mm"
include "breq1.mm"
include "cbvrexv.mm"
include "cbvrabcsf.mm"
include "eqtri.mm"
include "elrab2.mm"
include "simprd.mm"
include "renegcl.mm"
include "ad2antlr.mm"
include "rspcva.mm"
include "ancoms.mm"
include "simpllr.mm"
include "ad4ant14.mm"
include "lenegd.mm"
include "mpbid.mm"
include "ralrimiva.mm"
include "breq2.mm"
include "rspcev.mm"
include "ex.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "suprclrnmpt.mm"
include "wal.mm"
include "w3a.mm"
include "3ad2ant2.mm"
include "nfii1.mm"
include "nfel.mm"
include "nfan.mm"
include "nfel1.mm"
include "nfra1.mm"
include "nf3an.mm"
include "simpl2.mm"
include "simpll.mm"
include "3adant3.mm"
include "simp3.mm"
include "syl3anc.mm"
include "3ad2antl1.mm"
include "rspa.mm"
include "3ad2antl3.mm"
include "leneg.mm"
include "biimp3a.mm"
include "ralrimi.mm"
include "3exp.mm"
include "rexlimd.mm"
include "recn.mm"
include "negnegd.mm"
include "3ad2ant1.mm"
include "breqtrd.mm"
include "rexlimdv.mm"
include "impbid.mm"
include "rabbida.mm"
include "alrimi.mm"
include "mpteq12f.mm"
include "3expa.mm"
include "feqmptd.mm"
include "eqcomd.mm"
include "eqeltrd.mm"
include "smfneg.mm"
include "smfsupmpt.mm"

theorem smfinflem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cS: class S
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vm: setvar m
  let vw: setvar w
  let vz: setvar z
  let vk: setvar k
  assume smfinflem.m: |- ( ph -> M e. ZZ )
  assume smfinflem.z: |- Z = ( ZZ>= ` M )
  assume smfinflem.s: |- ( ph -> S e. SAlg )
  assume smfinflem.f: |- ( ph -> F : Z --> ( SMblFn ` S ) )
  assume smfinflem.d: |- D = { x e. |^|_ n e. Z dom ( F ` n ) | E. y e. RR A. n e. Z y <_ ( ( F ` n ) ` x ) }
  assume smfinflem.g: |- G = ( x e. D |-> inf ( ran ( n e. Z |-> ( ( F ` n ) ` x ) ) , RR , < ) )

  disjoint D n
  disjoint D x
  disjoint D y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint S n
  disjoint Z n
  disjoint Z x
  disjoint Z y
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint D m
  disjoint D w
  disjoint D z
  disjoint m n
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n w
  disjoint n z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint F m
  disjoint F w
  disjoint F z
  disjoint M m
  disjoint S m
  disjoint S z
  disjoint Z m
  disjoint Z w
  disjoint Z z
  disjoint m ph
  disjoint ph w
  disjoint ph z
  disjoint k x
  assert |- ( ph -> G e. ( SMblFn ` S ) )

  proof
    wph
    cG
    vx
    cD
    vn
    cZ
    vx
    cv
    #
    vn
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cneg
    #
    cmpt
    crn
    cr
    clt
    csup
    #
    cneg
    #
    cmpt
    #
    cS
    csmblfn
    cfv
    #
    wph
    cG
    vx
    cD
    vn
    cZ
    @3
    cmpt
    crn
    cr
    clt
    cinf
    #
    cmpt
    #
    @7
    cG
    @10
    wceq
    wph
    smfinflem.g
    a1i
    wph
    vx
    cD
    @9
    @6
    wph
    @0
    cD
    wcel
    #
    wa
    #
    vn
    vy
    cZ
    @3
    @12
    vn
    nfv
    #
    wph
    cZ
    c0
    wne
    @11
    wph
    cM
    cZ
    smfinflem.m
    smfinflem.z
    uzn0d
    #
    adantr
    #
    @12
    @1
    cZ
    wcel
    #
    wa
    #
    @2
    cdm
    #
    cr
    @0
    @2
    wph
    @16
    @18
    cr
    @2
    wf
    #
    @11
    wph
    @16
    wa
    #
    @18
    cS
    @2
    wph
    cS
    csalg
    wcel
    @16
    smfinflem.s
    adantr
    #
    wph
    cZ
    @8
    @1
    cF
    smfinflem.f
    ffvelrnda
    #
    @18
    eqid
    smff
    #
    adantlr
    @11
    @16
    @0
    @18
    wcel
    #
    wph
    @11
    @16
    wa
    @0
    vn
    cZ
    @18
    ciin
    #
    wcel
    #
    @16
    @24
    @11
    @26
    @16
    @11
    vy
    cv
    #
    @3
    cle
    wbr
    #
    vn
    cZ
    wral
    #
    vy
    cr
    wrex
    #
    vx
    @25
    crab
    #
    @25
    @0
    @30
    vx
    @25
    ssrab2
    @11
    @0
    @31
    wcel
    #
    cD
    @31
    @0
    smfinflem.d
    eleq2i
    biimpi
    #
    sseldi
    adantr
    @11
    @16
    simpr
    vn
    @0
    cZ
    @18
    eliinid
    #
    syl2anc
    adantll
    ffvelrnd
    #
    @11
    @30
    wph
    @11
    @32
    @30
    @33
    @30
    vx
    @25
    rabidim2
    syl
    adantl
    infnsuprnmpt
    mpteq2dva
    eqtrd
    wph
    vx
    cD
    @5
    cS
    cvv
    wph
    vx
    nfv
    #
    smfinflem.s
    wph
    @30
    vx
    @25
    cD
    cvv
    smfinflem.d
    wph
    vn
    cZ
    @18
    cvv
    @14
    @18
    cvv
    wcel
    #
    vn
    cZ
    wral
    wph
    @37
    vn
    cZ
    @2
    @1
    cF
    fvex
    dmex
    #
    rgenw
    a1i
    iinexd
    rabexd
    @12
    vn
    vy
    cZ
    @4
    @13
    @15
    @17
    @3
    @35
    renegcld
    @12
    vz
    cv
    #
    @0
    vm
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cle
    wbr
    #
    vm
    cZ
    wral
    #
    vz
    cr
    wrex
    #
    @4
    @27
    cle
    wbr
    #
    vn
    cZ
    wral
    #
    vy
    cr
    wrex
    #
    @11
    @45
    wph
    @11
    @0
    vm
    cZ
    @41
    cdm
    #
    ciin
    #
    wcel
    #
    @45
    @11
    @51
    @45
    wa
    @39
    vw
    cv
    #
    @41
    cfv
    #
    cle
    wbr
    #
    vm
    cZ
    wral
    #
    vz
    cr
    wrex
    #
    @45
    vw
    @0
    @50
    cD
    @52
    @0
    wceq
    #
    @55
    @44
    vz
    cr
    @57
    @54
    @43
    vm
    cZ
    @57
    @53
    @42
    @39
    cle
    @52
    @0
    @41
    fveq2
    breq2d
    ralbidv
    rexbidv
    cD
    @31
    @56
    vw
    @50
    crab
    smfinflem.d
    @30
    @56
    vx
    vw
    @25
    @50
    vw
    @25
    nfcv
    vm
    vx
    cZ
    @49
    vx
    cZ
    nfcv
    vx
    @41
    vx
    @41
    nfcv
    nfdm
    nfiin
    @30
    vw
    nfv
    @56
    vx
    nfv
    @25
    @50
    wceq
    @0
    @52
    wceq
    #
    vn
    vm
    cZ
    @18
    @49
    vm
    @18
    nfcv
    vn
    @41
    vn
    @41
    nfcv
    #
    nfdm
    @1
    @40
    wceq
    #
    @2
    @41
    @1
    @40
    cF
    fveq2
    #
    dmeqd
    cbviin
    a1i
    @58
    @30
    @27
    @53
    cle
    wbr
    #
    vm
    cZ
    wral
    #
    vy
    cr
    wrex
    #
    @56
    @58
    @29
    @63
    vy
    cr
    @58
    @29
    @27
    @52
    @2
    cfv
    #
    cle
    wbr
    #
    vn
    cZ
    wral
    #
    @63
    @58
    @28
    @66
    vn
    cZ
    @58
    @3
    @65
    @27
    cle
    @0
    @52
    @2
    fveq2
    breq2d
    ralbidv
    @67
    @63
    wb
    @58
    @66
    @62
    vn
    vm
    cZ
    @66
    vm
    nfv
    vn
    @27
    @53
    cle
    vn
    @27
    nfcv
    #
    vn
    cle
    nfcv
    vn
    @52
    @41
    @59
    vn
    @52
    nfcv
    nffv
    nfbr
    @60
    @65
    @53
    @27
    cle
    @60
    @52
    @2
    @41
    @61
    fveq1d
    breq2d
    cbvral
    a1i
    bitrd
    rexbidv
    @64
    @56
    wb
    @58
    @63
    @55
    vy
    vz
    cr
    @27
    @39
    wceq
    @62
    @54
    vm
    cZ
    @27
    @39
    @53
    cle
    breq1
    ralbidv
    cbvrexv
    a1i
    bitrd
    cbvrabcsf
    eqtri
    elrab2
    biimpi
    simprd
    adantl
    @12
    @44
    @48
    vz
    cr
    @12
    @39
    cr
    wcel
    #
    wa
    #
    @44
    @48
    @70
    @44
    wa
    #
    @39
    cneg
    #
    cr
    wcel
    #
    @4
    @72
    cle
    wbr
    #
    vn
    cZ
    wral
    #
    @48
    @69
    @73
    @12
    @44
    @39
    renegcl
    #
    ad2antlr
    @71
    @74
    vn
    cZ
    @71
    @16
    wa
    #
    @39
    @3
    cle
    wbr
    #
    @74
    @44
    @16
    @78
    @70
    @16
    @44
    @78
    @43
    @78
    vm
    @1
    cZ
    @40
    @1
    wceq
    #
    @42
    @3
    @39
    cle
    @79
    @0
    @41
    @2
    @40
    @1
    cF
    fveq2
    fveq1d
    breq2d
    rspcva
    ancoms
    adantll
    @77
    @39
    @3
    @12
    @69
    @44
    @16
    simpllr
    @12
    @16
    @3
    cr
    wcel
    #
    @69
    @44
    @35
    ad4ant14
    lenegd
    mpbid
    ralrimiva
    @47
    @75
    vy
    @72
    cr
    @27
    @72
    wceq
    #
    @46
    @74
    vn
    cZ
    @27
    @72
    @4
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    ex
    rexlimdva
    mpd
    suprclrnmpt
    wph
    vx
    cD
    @5
    cmpt
    #
    vx
    @4
    @39
    cle
    wbr
    #
    vn
    cZ
    wral
    #
    vz
    cr
    wrex
    #
    vx
    @25
    crab
    #
    @5
    cmpt
    #
    @8
    wph
    cD
    @86
    wceq
    #
    vx
    wal
    @5
    @5
    wceq
    #
    vx
    cD
    wral
    #
    @82
    @87
    wceq
    wph
    @88
    vx
    @36
    wph
    cD
    @31
    @86
    cD
    @31
    wceq
    wph
    smfinflem.d
    a1i
    wph
    @30
    @85
    vx
    @25
    @36
    wph
    @26
    wa
    #
    @30
    @85
    @91
    @29
    @85
    vy
    cr
    @91
    vy
    nfv
    @85
    vy
    nfv
    @91
    @27
    cr
    wcel
    #
    @29
    @85
    @91
    @92
    @29
    w3a
    #
    @27
    cneg
    #
    cr
    wcel
    #
    @4
    @94
    cle
    wbr
    #
    vn
    cZ
    wral
    #
    @85
    @92
    @91
    @95
    @29
    @27
    renegcl
    3ad2ant2
    @93
    @96
    vn
    cZ
    @91
    @92
    @29
    vn
    wph
    @26
    vn
    wph
    vn
    nfv
    #
    vn
    @0
    @25
    vn
    @0
    nfcv
    vn
    cZ
    @18
    nfii1
    nfel
    nfan
    #
    vn
    @27
    cr
    @68
    nfel1
    @28
    vn
    cZ
    nfra1
    nf3an
    @93
    @16
    @96
    @93
    @16
    wa
    @92
    @80
    @28
    @96
    @91
    @92
    @29
    @16
    simpl2
    @91
    @92
    @16
    @80
    @29
    @91
    @16
    wa
    wph
    @16
    @24
    @80
    wph
    @26
    @16
    simpll
    @91
    @16
    simpr
    @26
    @16
    @24
    wph
    @34
    adantll
    wph
    @16
    @24
    w3a
    #
    @18
    cr
    @0
    @2
    wph
    @16
    @19
    @24
    @23
    3adant3
    wph
    @16
    @24
    simp3
    ffvelrnd
    #
    syl3anc
    #
    3ad2antl1
    @29
    @91
    @16
    @28
    @92
    @28
    vn
    cZ
    rspa
    3ad2antl3
    @92
    @80
    @28
    @96
    @27
    @3
    leneg
    biimp3a
    syl3anc
    ex
    ralrimi
    @84
    @97
    vz
    @94
    cr
    @39
    @94
    wceq
    @83
    @96
    vn
    cZ
    @39
    @94
    @4
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    3exp
    rexlimd
    @91
    @84
    @30
    vz
    cr
    @91
    @69
    @84
    @30
    @91
    @69
    @84
    w3a
    #
    @73
    @72
    @3
    cle
    wbr
    #
    vn
    cZ
    wral
    #
    @30
    @69
    @91
    @73
    @84
    @76
    3ad2ant2
    @103
    @104
    vn
    cZ
    @91
    @69
    @84
    vn
    @99
    @69
    vn
    nfv
    @83
    vn
    cZ
    nfra1
    nf3an
    @103
    @16
    @104
    @103
    @16
    wa
    @80
    @69
    @83
    @104
    @91
    @69
    @16
    @80
    @84
    @102
    3ad2antl1
    @91
    @69
    @84
    @16
    simpl2
    @84
    @91
    @16
    @83
    @69
    @83
    vn
    cZ
    rspa
    3ad2antl3
    @80
    @69
    @83
    w3a
    #
    @72
    @4
    cneg
    #
    @3
    cle
    @106
    @83
    @72
    @107
    cle
    wbr
    #
    @80
    @69
    @83
    simp3
    @80
    @69
    @83
    @108
    wb
    #
    @83
    @80
    @69
    wa
    @4
    cr
    wcel
    #
    @69
    @109
    @80
    @110
    @69
    @3
    renegcl
    adantr
    @80
    @69
    simpr
    @4
    @39
    leneg
    syl2anc
    3adant3
    mpbid
    @80
    @69
    @107
    @3
    wceq
    @83
    @80
    @3
    @3
    recn
    negnegd
    3ad2ant1
    breqtrd
    syl3anc
    ex
    ralrimi
    @29
    @105
    vy
    @72
    cr
    @81
    @28
    @104
    vn
    cZ
    @27
    @72
    @3
    cle
    breq1
    ralbidv
    rspcev
    syl2anc
    3exp
    rexlimdv
    impbid
    rabbida
    eqtrd
    alrimi
    @90
    wph
    @89
    vx
    cD
    @5
    eqid
    rgenw
    a1i
    vx
    cD
    @5
    @86
    @5
    mpteq12f
    syl2anc
    wph
    vx
    vz
    @18
    @4
    @86
    cS
    vn
    @87
    cM
    cr
    cZ
    @98
    @36
    wph
    vz
    nfv
    smfinflem.m
    smfinflem.z
    smfinflem.s
    @100
    @3
    @101
    renegcld
    @20
    vx
    @18
    @3
    cS
    cvv
    @20
    vx
    nfv
    @21
    @37
    @20
    @38
    a1i
    wph
    @16
    @24
    @80
    @101
    3expa
    @20
    vx
    @18
    @3
    cmpt
    #
    @2
    @8
    @20
    @2
    @111
    @20
    vx
    @18
    cr
    @2
    @23
    feqmptd
    eqcomd
    @22
    eqeltrd
    smfneg
    @86
    eqid
    @87
    eqid
    smfsupmpt
    eqeltrd
    smfneg
    eqeltrd
end
