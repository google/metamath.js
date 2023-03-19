include "wcel.mm"
include "cvv.mm"
include "cfbas.mm"
include "cfv.mm"
include "elex.mm"
include "crn.mm"
include "cpw.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wnel.mm"
include "cv.mm"
include "cin.mm"
include "wral.mm"
include "w3a.mm"
include "wf.mm"
include "crab.mm"
include "wa.mm"
include "ssrab2.mm"
include "wb.mm"
include "cfn.mm"
include "pwexg.mm"
include "inex1g.mm"
include "syl.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "elpw2g.mm"
include "mpbiri.mm"
include "fmptd.mm"
include "frn.mm"
include "wceq.mm"
include "wrex.mm"
include "0ss.mm"
include "0fin.mm"
include "elfpw.mm"
include "mpbir2an.mm"
include "eleqtrri.mm"
include "rgenw.mm"
include "rabid2.mm"
include "sseq1.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "rspcev.mm"
include "mp2an.mm"
include "elrnmpt.mm"
include "ne0i.mm"
include "wn.mm"
include "simpr.mm"
include "ssid.mm"
include "sseq2.mm"
include "sylancl.mm"
include "rabn0.mm"
include "sylibr.mm"
include "necomd.mm"
include "neneqd.mm"
include "nrexdv.mm"
include "0ex.mm"
include "ax-mp.mm"
include "sylnibr.mm"
include "df-nel.mm"
include "cun.mm"
include "simplbi.mm"
include "eleq2s.mm"
include "anim12i.mm"
include "unss.mm"
include "sylib.mm"
include "simprbi.mm"
include "unfi.mm"
include "syl2an.mm"
include "sylanbrc.mm"
include "adantl.mm"
include "syl6eleqr.mm"
include "eqidd.mm"
include "rabbidv.mm"
include "eqeq2d.mm"
include "syl2anc.mm"
include "rabexg.mm"
include "cmpt.mm"
include "weq.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "mpbird.mm"
include "pwidg.mm"
include "inelcm.mm"
include "ralrimivva.mm"
include "ralrimivw.mm"
include "ineq1.mm"
include "inrab.mm"
include "rabbii.mm"
include "syl6eq.mm"
include "pweqd.mm"
include "ineq2d.mm"
include "neeq1d.mm"
include "ralrnmpt.mm"
include "ineq2.mm"
include "3jca.mm"
include "isfbas.mm"
include "mpbir2and.mm"
include "3syl.mm"

theorem tsmsfbas
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cS: class S
  let cF: class F
  let cL: class L
  let cW: class W
  let va: setvar a
  let vu: setvar u
  let vv: setvar v
  let vb: setvar b
  assume tsmsfbas.s: |- S = ( ~P A i^i Fin )
  assume tsmsfbas.f: |- F = ( z e. S |-> { y e. S | z C_ y } )
  assume tsmsfbas.l: |- L = ran F
  assume tsmsfbas.a: |- ( ph -> A e. W )

  disjoint A z
  disjoint y z
  disjoint S y
  disjoint S z
  disjoint a u
  disjoint a v
  disjoint a z
  disjoint A a
  disjoint u v
  disjoint u z
  disjoint A u
  disjoint v z
  disjoint A v
  disjoint a b
  disjoint F a
  disjoint b u
  disjoint b v
  disjoint F b
  disjoint F u
  disjoint F v
  disjoint a y
  disjoint S a
  disjoint b y
  disjoint b z
  disjoint S b
  disjoint u y
  disjoint S u
  disjoint v y
  disjoint S v
  assert |- ( ph -> L e. ( fBas ` S ) )

  proof
    wph
    cA
    cW
    wcel
    cA
    cvv
    wcel
    #
    cL
    cS
    cfbas
    cfv
    #
    wcel
    tsmsfbas.a
    cA
    cW
    elex
    @0
    cL
    cF
    crn
    #
    @1
    tsmsfbas.l
    @0
    @2
    @1
    wcel
    #
    @2
    cS
    cpw
    #
    wss
    #
    @2
    c0
    wne
    #
    c0
    @2
    wnel
    #
    @2
    va
    cv
    #
    vb
    cv
    #
    cin
    #
    cpw
    #
    cin
    #
    c0
    wne
    #
    vb
    @2
    wral
    #
    va
    @2
    wral
    #
    w3a
    #
    @0
    cS
    @4
    cF
    wf
    @5
    @0
    vz
    cS
    vz
    cv
    #
    vy
    cv
    #
    wss
    #
    vy
    cS
    crab
    #
    @4
    cF
    @0
    @17
    cS
    wcel
    #
    wa
    #
    @20
    @4
    wcel
    #
    @20
    cS
    wss
    #
    @19
    vy
    cS
    ssrab2
    @22
    cS
    cvv
    wcel
    #
    @23
    @24
    wb
    @0
    @25
    @21
    @0
    cS
    cA
    cpw
    #
    cfn
    cin
    #
    cvv
    tsmsfbas.s
    @0
    @26
    cvv
    wcel
    @27
    cvv
    wcel
    cA
    cvv
    pwexg
    @26
    cfn
    cvv
    inex1g
    syl
    syl5eqel
    #
    adantr
    @20
    cS
    cvv
    elpw2g
    syl
    mpbiri
    tsmsfbas.f
    fmptd
    cS
    @4
    cF
    frn
    syl
    @0
    @6
    @7
    @15
    @0
    cS
    @2
    wcel
    #
    @6
    @0
    @29
    cS
    @20
    wceq
    #
    vz
    cS
    wrex
    #
    c0
    cS
    wcel
    c0
    @18
    wss
    #
    vy
    cS
    wral
    #
    @31
    c0
    @27
    cS
    c0
    @27
    wcel
    c0
    cA
    wss
    c0
    cfn
    wcel
    cA
    0ss
    0fin
    c0
    cA
    elfpw
    mpbir2an
    tsmsfbas.s
    eleqtrri
    @32
    vy
    cS
    @18
    0ss
    rgenw
    @30
    @33
    vz
    c0
    cS
    @30
    @19
    vy
    cS
    wral
    @17
    c0
    wceq
    #
    @33
    @19
    vy
    cS
    rabid2
    @34
    @19
    @32
    vy
    cS
    @17
    c0
    @18
    sseq1
    ralbidv
    syl5bb
    rspcev
    mp2an
    @0
    @25
    @29
    @31
    wb
    @28
    vz
    cS
    @20
    cS
    cF
    cvv
    tsmsfbas.f
    elrnmpt
    syl
    mpbiri
    @2
    cS
    ne0i
    syl
    @0
    c0
    @2
    wcel
    #
    wn
    @7
    @0
    c0
    @20
    wceq
    #
    vz
    cS
    wrex
    #
    @35
    @0
    @36
    vz
    cS
    @22
    c0
    @20
    @22
    @20
    c0
    @22
    @19
    vy
    cS
    wrex
    #
    @20
    c0
    wne
    @22
    @21
    @17
    @17
    wss
    #
    @38
    @0
    @21
    simpr
    @17
    ssid
    @19
    @39
    vy
    @17
    cS
    @18
    @17
    @17
    sseq2
    rspcev
    sylancl
    @19
    vy
    cS
    rabn0
    sylibr
    necomd
    neneqd
    nrexdv
    c0
    cvv
    wcel
    @35
    @37
    wb
    0ex
    vz
    cS
    @20
    c0
    cF
    cvv
    tsmsfbas.f
    elrnmpt
    ax-mp
    sylnibr
    c0
    @2
    df-nel
    sylibr
    @0
    @15
    @2
    @8
    vv
    cv
    #
    @18
    wss
    #
    vy
    cS
    crab
    #
    cin
    #
    cpw
    #
    cin
    #
    c0
    wne
    #
    vv
    cS
    wral
    #
    va
    @2
    wral
    #
    @0
    @48
    @2
    vu
    cv
    #
    @40
    cun
    #
    @18
    wss
    #
    vy
    cS
    crab
    #
    cpw
    #
    cin
    #
    c0
    wne
    #
    vv
    cS
    wral
    #
    vu
    cS
    wral
    #
    @0
    @55
    vu
    vv
    cS
    cS
    @0
    @49
    cS
    wcel
    #
    @40
    cS
    wcel
    #
    wa
    #
    wa
    #
    @52
    @2
    wcel
    #
    @52
    @53
    wcel
    #
    @55
    @61
    @62
    @52
    @8
    @18
    wss
    #
    vy
    cS
    crab
    #
    wceq
    #
    va
    cS
    wrex
    #
    @61
    @50
    cS
    wcel
    @52
    @52
    wceq
    #
    @67
    @61
    @50
    @27
    cS
    @60
    @50
    @27
    wcel
    #
    @0
    @60
    @50
    cA
    wss
    #
    @50
    cfn
    wcel
    #
    @69
    @60
    @49
    cA
    wss
    #
    @40
    cA
    wss
    #
    wa
    @70
    @58
    @72
    @59
    @73
    @72
    @49
    @27
    cS
    @49
    @27
    wcel
    #
    @72
    @49
    cfn
    wcel
    #
    @49
    cA
    elfpw
    #
    simplbi
    tsmsfbas.s
    eleq2s
    @73
    @40
    @27
    cS
    @40
    @27
    wcel
    #
    @73
    @40
    cfn
    wcel
    #
    @40
    cA
    elfpw
    #
    simplbi
    tsmsfbas.s
    eleq2s
    anim12i
    @49
    @40
    cA
    unss
    sylib
    @58
    @75
    @78
    @71
    @59
    @75
    @49
    @27
    cS
    @74
    @72
    @75
    @76
    simprbi
    tsmsfbas.s
    eleq2s
    @78
    @40
    @27
    cS
    @77
    @73
    @78
    @79
    simprbi
    tsmsfbas.s
    eleq2s
    @49
    @40
    unfi
    syl2an
    @50
    cA
    elfpw
    sylanbrc
    adantl
    tsmsfbas.s
    syl6eleqr
    @61
    @52
    eqidd
    @66
    @68
    va
    @50
    cS
    @8
    @50
    wceq
    #
    @65
    @52
    @52
    @80
    @64
    @51
    vy
    cS
    @8
    @50
    @18
    sseq1
    rabbidv
    eqeq2d
    rspcev
    syl2anc
    @61
    @52
    cvv
    wcel
    #
    @62
    @67
    wb
    @61
    @25
    @81
    @0
    @25
    @60
    @28
    adantr
    @51
    vy
    cS
    cvv
    rabexg
    syl
    #
    va
    cS
    @65
    @52
    cF
    cvv
    cF
    vz
    cS
    @20
    cmpt
    #
    va
    cS
    @65
    cmpt
    tsmsfbas.f
    vz
    va
    cS
    @20
    @65
    vz
    va
    weq
    @19
    @64
    vy
    cS
    @17
    @8
    @18
    sseq1
    rabbidv
    cbvmptv
    eqtri
    elrnmpt
    syl
    mpbird
    @61
    @81
    @63
    @82
    @52
    cvv
    pwidg
    syl
    @52
    @2
    @53
    inelcm
    syl2anc
    ralrimivva
    @0
    @49
    @18
    wss
    #
    vy
    cS
    crab
    #
    cvv
    wcel
    #
    vu
    cS
    wral
    @48
    @57
    wb
    @0
    @86
    vu
    cS
    @0
    @25
    @86
    @28
    @84
    vy
    cS
    cvv
    rabexg
    syl
    ralrimivw
    @47
    @56
    vu
    va
    cS
    @85
    cF
    cvv
    cF
    @83
    vu
    cS
    @85
    cmpt
    tsmsfbas.f
    vz
    vu
    cS
    @20
    @85
    vz
    vu
    weq
    @19
    @84
    vy
    cS
    @17
    @49
    @18
    sseq1
    rabbidv
    cbvmptv
    eqtri
    @8
    @85
    wceq
    #
    @46
    @55
    vv
    cS
    @87
    @45
    @54
    c0
    @87
    @44
    @53
    @2
    @87
    @43
    @52
    @87
    @43
    @85
    @42
    cin
    #
    @52
    @8
    @85
    @42
    ineq1
    @88
    @84
    @41
    wa
    #
    vy
    cS
    crab
    @52
    @84
    @41
    vy
    cS
    inrab
    @89
    @51
    vy
    cS
    @49
    @40
    @18
    unss
    rabbii
    eqtri
    syl6eq
    pweqd
    ineq2d
    neeq1d
    ralbidv
    ralrnmpt
    syl
    mpbird
    @0
    @14
    @47
    va
    @2
    @0
    @42
    cvv
    wcel
    #
    vv
    cS
    wral
    @14
    @47
    wb
    @0
    @90
    vv
    cS
    @0
    @25
    @90
    @28
    @41
    vy
    cS
    cvv
    rabexg
    syl
    ralrimivw
    @13
    @46
    vv
    vb
    cS
    @42
    cF
    cvv
    cF
    @83
    vv
    cS
    @42
    cmpt
    tsmsfbas.f
    vz
    vv
    cS
    @20
    @42
    vz
    vv
    weq
    @19
    @41
    vy
    cS
    @17
    @40
    @18
    sseq1
    rabbidv
    cbvmptv
    eqtri
    @9
    @42
    wceq
    #
    @12
    @45
    c0
    @91
    @11
    @44
    @2
    @91
    @10
    @43
    @9
    @42
    @8
    ineq2
    pweqd
    ineq2d
    neeq1d
    ralrnmpt
    syl
    ralbidv
    mpbird
    3jca
    @0
    @25
    @3
    @5
    @16
    wa
    wb
    @28
    va
    vb
    cvv
    cS
    @2
    isfbas
    syl
    mpbir2and
    syl5eqel
    3syl
end
