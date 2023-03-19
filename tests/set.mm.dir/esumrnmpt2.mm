include "c0.mm"
include "wceq.mm"
include "crab.mm"
include "cmpt.mm"
include "crn.mm"
include "wn.mm"
include "cun.mm"
include "cesum.mm"
include "cxad.mm"
include "co.mm"
include "cvv.mm"
include "nfrab1.mm"
include "wss.mm"
include "ssrab2.mm"
include "a1i.mm"
include "ssexd.mm"
include "cv.mm"
include "wcel.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "sselda.mm"
include "syldan.mm"
include "wa.mm"
include "csn.mm"
include "rabid.mm"
include "simprbi.mm"
include "adantl.mm"
include "wb.mm"
include "elsng.mm"
include "syl.mm"
include "mtbird.mm"
include "eldifd.mm"
include "wdisj.mm"
include "nfcv.mm"
include "disjss1f.mm"
include "sylc.mm"
include "esumrnmpt.mm"
include "cle.mm"
include "wbr.mm"
include "wrex.mm"
include "nfv.mm"
include "snex.mm"
include "velsn.mm"
include "biimpi.mm"
include "nfre1.mm"
include "nfan.mm"
include "simpllr.mm"
include "simpr.mm"
include "eqtr4d.mm"
include "simp-4l.mm"
include "simplr.mm"
include "syl21anc.mm"
include "eqtrd.mm"
include "r19.29af2.mm"
include "0e0iccpnf.mm"
include "syl6eqel.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfel.mm"
include "ad2antlr.mm"
include "sylibr.mm"
include "vex.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "r19.29af.mm"
include "ex.mm"
include "ssrdv.mm"
include "adantr.mm"
include "esummono.mm"
include "0ex.mm"
include "esumsn.mm"
include "breqtrd.mm"
include "nfn.mm"
include "wne.mm"
include "rabn0.mm"
include "necon1bi.mm"
include "mpteq12df.mm"
include "mpt0.mm"
include "syl6eq.mm"
include "rneqd.mm"
include "rn0.mm"
include "esumeq1d.mm"
include "esumnul.mm"
include "0le0.mm"
include "syl6eqbr.mm"
include "pm2.61dan.mm"
include "wral.mm"
include "mptexgf.mm"
include "rnexg.mm"
include "3syl.mm"
include "simplll.mm"
include "adantlr.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "esumcl.mm"
include "cxr.mm"
include "elxrge0.mm"
include "jca.mm"
include "iccssxr.mm"
include "sseldi.mm"
include "sselii.mm"
include "xrletri3.mm"
include "mpbird.mm"
include "oveq1d.mm"
include "xaddid2.mm"
include "simpl.mm"
include "esumeq2d.mm"
include "esum0.mm"
include "3eqtr4d.mm"
include "cin.mm"
include "ssrin.mm"
include "incom.mm"
include "neqned.mm"
include "necomd.mm"
include "neneqd.mm"
include "nrex.mm"
include "mtbir.mm"
include "disjsn.mm"
include "mpbir.mm"
include "eqtr3i.mm"
include "syl6sseq.mm"
include "ss0.mm"
include "esumsplit.mm"
include "rabnc.mm"
include "rabxm.mm"
include "mpteq12i.mm"
include "mptun.mm"
include "eqtri.mm"
include "rneqi.mm"
include "rnun.mm"

theorem esumrnmpt2
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let cV: class V
  let cW: class W
  assume esumrnmpt2.1: |- ( y = B -> C = D )
  assume esumrnmpt2.2: |- ( ph -> A e. V )
  assume esumrnmpt2.3: |- ( ( ph /\ k e. A ) -> D e. ( 0 [,] +oo ) )
  assume esumrnmpt2.4: |- ( ( ph /\ k e. A ) -> B e. W )
  assume esumrnmpt2.5: |- ( ( ( ph /\ k e. A ) /\ B = (/) ) -> D = 0 )
  assume esumrnmpt2.6: |- ( ph -> Disj_ k e. A B )

  disjoint A k
  disjoint A y
  disjoint k y
  disjoint B y
  disjoint C k
  disjoint D y
  disjoint W k
  disjoint k ph
  disjoint ph y
  assert |- ( ph -> sum* y e. ran ( k e. A |-> B ) C = sum* k e. A D )

  proof
    wph
    vk
    cB
    c0
    wceq
    #
    vk
    cA
    crab
    #
    cB
    cmpt
    #
    crn
    #
    vk
    @0
    wn
    #
    vk
    cA
    crab
    #
    cB
    cmpt
    #
    crn
    #
    cun
    #
    cC
    vy
    cesum
    #
    @1
    @5
    cun
    #
    cD
    vk
    cesum
    #
    vk
    cA
    cB
    cmpt
    #
    crn
    #
    cC
    vy
    cesum
    cA
    cD
    vk
    cesum
    wph
    @3
    cC
    vy
    cesum
    #
    @7
    cC
    vy
    cesum
    #
    cxad
    co
    #
    @1
    cD
    vk
    cesum
    #
    @5
    cD
    vk
    cesum
    #
    cxad
    co
    #
    @9
    @11
    wph
    @15
    @18
    @16
    @19
    wph
    vy
    @5
    cB
    cC
    cD
    vk
    cvv
    cW
    @4
    vk
    cA
    nfrab1
    #
    esumrnmpt2.1
    wph
    @5
    cA
    cV
    esumrnmpt2.2
    @5
    cA
    wss
    #
    wph
    @4
    vk
    cA
    ssrab2
    a1i
    #
    ssexd
    #
    wph
    vk
    cv
    #
    @5
    wcel
    #
    @24
    cA
    wcel
    #
    cD
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    wph
    @5
    cA
    @24
    @22
    sselda
    #
    esumrnmpt2.3
    syldan
    #
    wph
    @25
    wa
    #
    cB
    cW
    c0
    csn
    #
    wph
    @25
    @26
    cB
    cW
    wcel
    #
    @29
    esumrnmpt2.4
    syldan
    #
    @31
    cB
    @32
    wcel
    #
    @0
    @25
    @4
    wph
    @25
    @26
    @4
    @4
    vk
    cA
    rabid
    simprbi
    #
    adantl
    @31
    @33
    @35
    @0
    wb
    @34
    cB
    c0
    cW
    elsng
    syl
    mtbird
    eldifd
    wph
    @21
    vk
    cA
    cB
    wdisj
    vk
    @5
    cB
    wdisj
    @22
    esumrnmpt2.6
    vk
    @5
    cA
    cB
    @20
    vk
    cA
    nfcv
    disjss1f
    sylc
    esumrnmpt
    #
    wph
    @16
    cc0
    @15
    cxad
    co
    #
    @15
    wph
    @14
    cc0
    @15
    cxad
    wph
    @14
    cc0
    wceq
    #
    @14
    cc0
    cle
    wbr
    #
    cc0
    @14
    cle
    wbr
    #
    wa
    #
    wph
    @40
    @41
    wph
    @0
    vk
    cA
    wrex
    #
    @40
    wph
    @43
    wa
    #
    @14
    @32
    cC
    vy
    cesum
    cc0
    cle
    @44
    @3
    cC
    @32
    vy
    cvv
    @44
    vy
    nfv
    @32
    cvv
    wcel
    @44
    c0
    snex
    a1i
    @44
    vy
    cv
    #
    @32
    wcel
    #
    wa
    cC
    cc0
    @27
    @44
    @46
    @45
    c0
    wceq
    #
    cC
    cc0
    wceq
    #
    @46
    @47
    @44
    @46
    @47
    vy
    c0
    velsn
    #
    biimpi
    adantl
    @44
    @47
    wa
    #
    @0
    @48
    vk
    cA
    @44
    @47
    vk
    wph
    @43
    vk
    wph
    vk
    nfv
    #
    @0
    vk
    cA
    nfre1
    #
    nfan
    @47
    vk
    nfv
    nfan
    @48
    vk
    nfv
    @50
    @26
    wa
    #
    @0
    wa
    #
    cC
    cD
    cc0
    @54
    @45
    cB
    wceq
    #
    cC
    cD
    wceq
    #
    @54
    @45
    c0
    cB
    @44
    @47
    @26
    @0
    simpllr
    @53
    @0
    simpr
    #
    eqtr4d
    esumrnmpt2.1
    syl
    @54
    wph
    @26
    @0
    cD
    cc0
    wceq
    #
    wph
    @43
    @47
    @26
    @0
    simp-4l
    @50
    @26
    @0
    simplr
    @57
    esumrnmpt2.5
    syl21anc
    eqtrd
    wph
    @43
    @47
    simplr
    r19.29af2
    #
    syldan
    0e0iccpnf
    syl6eqel
    wph
    @3
    @32
    wss
    #
    @43
    wph
    vy
    @3
    @32
    wph
    @45
    @3
    wcel
    #
    @46
    wph
    @61
    wa
    #
    @55
    @46
    vk
    @1
    wph
    @61
    vk
    @51
    vk
    @45
    @3
    vk
    @45
    nfcv
    #
    vk
    @2
    vk
    @1
    cB
    nfmpt1
    nfrn
    nfel
    nfan
    #
    @62
    @24
    @1
    wcel
    #
    wa
    #
    @55
    wa
    #
    @47
    @46
    @67
    @45
    cB
    c0
    @66
    @55
    simpr
    @65
    @0
    @62
    @55
    @65
    @26
    @0
    @0
    vk
    cA
    rabid
    simprbi
    #
    ad2antlr
    eqtrd
    @49
    sylibr
    @61
    @55
    vk
    @1
    wrex
    #
    wph
    @61
    @69
    @45
    cvv
    wcel
    #
    @61
    @69
    wb
    vy
    vex
    #
    vk
    @1
    cB
    @45
    @2
    cvv
    @2
    eqid
    elrnmpt
    ax-mp
    biimpi
    adantl
    #
    r19.29af
    ex
    ssrdv
    #
    adantr
    esummono
    @44
    cC
    cc0
    vy
    c0
    cvv
    @59
    c0
    cvv
    wcel
    #
    @44
    0ex
    a1i
    cc0
    @27
    wcel
    @44
    0e0iccpnf
    a1i
    esumsn
    breqtrd
    wph
    @43
    wn
    #
    wa
    @75
    @40
    wph
    @75
    simpr
    @75
    @14
    cc0
    cc0
    cle
    @75
    @14
    c0
    cC
    vy
    cesum
    cc0
    @75
    @3
    c0
    cC
    vy
    @75
    vy
    nfv
    @75
    @3
    c0
    crn
    c0
    @75
    @2
    c0
    @75
    @2
    vk
    c0
    cB
    cmpt
    c0
    @75
    vk
    @1
    cB
    c0
    cB
    @43
    vk
    @52
    nfn
    @0
    vk
    cA
    nfrab1
    #
    vk
    c0
    nfcv
    @43
    @1
    c0
    @1
    c0
    wne
    @43
    @0
    vk
    cA
    rabn0
    biimpi
    necon1bi
    cB
    cB
    wceq
    @75
    cB
    eqid
    #
    a1i
    mpteq12df
    vk
    cB
    mpt0
    syl6eq
    rneqd
    rn0
    syl6eq
    esumeq1d
    vy
    cC
    esumnul
    syl6eq
    0le0
    syl6eqbr
    syl
    pm2.61dan
    wph
    @14
    @27
    wcel
    #
    @41
    wph
    @3
    cvv
    wcel
    #
    cC
    @27
    wcel
    #
    vy
    @3
    wral
    @78
    wph
    @1
    cvv
    wcel
    #
    @2
    cvv
    wcel
    @79
    wph
    @1
    cA
    cV
    esumrnmpt2.2
    @1
    cA
    wss
    wph
    @0
    vk
    cA
    ssrab2
    a1i
    #
    ssexd
    #
    vk
    @1
    cB
    cvv
    @76
    mptexgf
    @2
    cvv
    rnexg
    3syl
    #
    wph
    @80
    vy
    @3
    @62
    @55
    @80
    vk
    @1
    @64
    @67
    cC
    cD
    @27
    @55
    @56
    @66
    esumrnmpt2.1
    adantl
    @67
    wph
    @26
    @28
    wph
    @61
    @65
    @55
    simplll
    @66
    @26
    @55
    wph
    @65
    @26
    @61
    wph
    @1
    cA
    @24
    @82
    sselda
    #
    adantlr
    adantr
    esumrnmpt2.3
    syl2anc
    eqeltrd
    @72
    r19.29af
    #
    ralrimiva
    @3
    cC
    vy
    cvv
    vy
    @3
    nfcv
    #
    esumcl
    syl2anc
    #
    @78
    @14
    cxr
    wcel
    #
    @41
    @14
    elxrge0
    simprbi
    syl
    jca
    wph
    @89
    cc0
    cxr
    wcel
    #
    @39
    @42
    wb
    wph
    @27
    cxr
    @14
    cc0
    cpnf
    iccssxr
    #
    @88
    sseldi
    @90
    wph
    @27
    cxr
    cc0
    @91
    0e0iccpnf
    sselii
    a1i
    @14
    cc0
    xrletri3
    syl2anc
    mpbird
    oveq1d
    wph
    @15
    cxr
    wcel
    @38
    @15
    wceq
    wph
    @15
    @18
    cxr
    @37
    wph
    @27
    cxr
    @18
    @91
    wph
    @5
    cvv
    wcel
    #
    @28
    vk
    @5
    wral
    @18
    @27
    wcel
    @23
    wph
    @28
    vk
    @5
    @30
    ralrimiva
    @5
    cD
    vk
    cvv
    @20
    esumcl
    syl2anc
    sseldi
    #
    eqeltrd
    @15
    xaddid2
    syl
    eqtrd
    wph
    @19
    cc0
    @18
    cxad
    co
    #
    @18
    wph
    @17
    cc0
    @18
    cxad
    wph
    @17
    @1
    cc0
    vk
    cesum
    #
    cc0
    wph
    @1
    cD
    cc0
    vk
    @51
    wph
    @58
    vk
    @1
    wph
    @65
    wa
    wph
    @26
    @0
    @58
    wph
    @65
    simpl
    @85
    @65
    @0
    wph
    @68
    adantl
    esumrnmpt2.5
    syl21anc
    ralrimiva
    esumeq2d
    wph
    @81
    @95
    cc0
    wceq
    @83
    @1
    vk
    cvv
    @76
    esum0
    syl
    eqtrd
    oveq1d
    wph
    @18
    cxr
    wcel
    @94
    @18
    wceq
    @93
    @18
    xaddid2
    syl
    eqtrd
    3eqtr4d
    wph
    @3
    @7
    cC
    vy
    wph
    vy
    nfv
    #
    @87
    vy
    @7
    nfcv
    @84
    wph
    @92
    @6
    cvv
    wcel
    @7
    cvv
    wcel
    @23
    vk
    @5
    cB
    cvv
    @20
    mptexgf
    @6
    cvv
    rnexg
    3syl
    wph
    @3
    @7
    cin
    #
    c0
    wss
    @97
    c0
    wceq
    wph
    @97
    @32
    @7
    cin
    #
    c0
    wph
    @60
    @97
    @98
    wss
    @73
    @3
    @32
    @7
    ssrin
    syl
    @7
    @32
    cin
    #
    @98
    c0
    @7
    @32
    incom
    @99
    c0
    wceq
    c0
    @7
    wcel
    #
    wn
    @100
    c0
    cB
    wceq
    #
    vk
    @5
    wrex
    #
    @101
    vk
    @5
    @25
    c0
    cB
    @25
    cB
    c0
    @25
    cB
    c0
    @36
    neqned
    necomd
    neneqd
    nrex
    @74
    @100
    @102
    wb
    0ex
    vk
    @5
    cB
    c0
    @6
    cvv
    @6
    eqid
    #
    elrnmpt
    ax-mp
    mtbir
    @7
    c0
    disjsn
    mpbir
    eqtr3i
    syl6sseq
    @97
    ss0
    syl
    @86
    wph
    @45
    @7
    wcel
    #
    wa
    #
    @55
    @80
    vk
    @5
    wph
    @104
    vk
    @51
    vk
    @45
    @7
    @63
    vk
    @6
    vk
    @5
    cB
    nfmpt1
    nfrn
    nfel
    nfan
    @105
    @25
    wa
    #
    @55
    wa
    #
    cC
    cD
    @27
    @55
    @56
    @106
    esumrnmpt2.1
    adantl
    @107
    wph
    @26
    @28
    wph
    @104
    @25
    @55
    simplll
    @106
    @26
    @55
    wph
    @25
    @26
    @104
    @29
    adantlr
    adantr
    esumrnmpt2.3
    syl2anc
    eqeltrd
    @104
    @55
    vk
    @5
    wrex
    #
    wph
    @104
    @108
    @70
    @104
    @108
    wb
    @71
    vk
    @5
    cB
    @45
    @6
    cvv
    @103
    elrnmpt
    ax-mp
    biimpi
    adantl
    r19.29af
    esumsplit
    wph
    @1
    @5
    cD
    vk
    @51
    @76
    @20
    @83
    @23
    @1
    @5
    cin
    c0
    wceq
    wph
    @0
    vk
    cA
    rabnc
    a1i
    wph
    @65
    @26
    @28
    @85
    esumrnmpt2.3
    syldan
    @30
    esumsplit
    3eqtr4d
    wph
    @13
    @8
    cC
    vy
    @96
    @13
    @8
    wceq
    wph
    @13
    @2
    @6
    cun
    #
    crn
    @8
    @12
    @109
    @12
    vk
    @10
    cB
    cmpt
    @109
    vk
    cA
    cB
    @10
    cB
    @0
    vk
    cA
    rabxm
    #
    @77
    mpteq12i
    vk
    @1
    @5
    cB
    mptun
    eqtri
    rneqi
    @2
    @6
    rnun
    eqtri
    a1i
    esumeq1d
    wph
    cA
    @10
    cD
    vk
    @51
    cA
    @10
    wceq
    wph
    @110
    a1i
    esumeq1d
    3eqtr4d
end
