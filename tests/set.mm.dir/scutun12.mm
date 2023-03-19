include "csslt.mm"
include "wbr.mm"
include "cscut.mm"
include "co.mm"
include "csn.mm"
include "w3a.mm"
include "cun.mm"
include "cv.mm"
include "cbday.mm"
include "cfv.mm"
include "wa.mm"
include "csur.mm"
include "crab.mm"
include "cima.mm"
include "cint.mm"
include "wceq.mm"
include "crio.mm"
include "wcel.mm"
include "simp1.mm"
include "scutcut.mm"
include "syl.mm"
include "simp2d.mm"
include "simp2.mm"
include "ssltun1.mm"
include "syl2anc.mm"
include "simp3d.mm"
include "simp3.mm"
include "ssltun2.mm"
include "c0.mm"
include "wne.mm"
include "ovex.mm"
include "snnz.mm"
include "sslttr.mm"
include "mp3an3.mm"
include "scutval.mm"
include "wss.mm"
include "wral.mm"
include "wrex.mm"
include "vex.mm"
include "elima.mm"
include "weq.mm"
include "sneq.mm"
include "breq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "rexrab.mm"
include "bitri.mm"
include "wi.mm"
include "wb.mm"
include "simplr.mm"
include "wfn.mm"
include "bdayfn.mm"
include "fnbrfvb.mm"
include "mpan.mm"
include "simpll1.mm"
include "scutbday.mm"
include "simprl.mm"
include "ssun1.mm"
include "sssslt1.mm"
include "mpan2.mm"
include "simprr.mm"
include "sssslt2.mm"
include "jca.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "ssrab2.mm"
include "fnfvima.mm"
include "mp3an12.mm"
include "intss1.mm"
include "eqsstrd.mm"
include "sseq2.mm"
include "biimpd.mm"
include "com12.mm"
include "sylbird.mm"
include "ex.mm"
include "impd.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "ssint.mm"
include "sylibr.mm"
include "simp1d.mm"
include "eqssd.mm"
include "wreu.mm"
include "conway.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "riota2.mm"
include "mpbid.mm"
include "eqcomd.mm"
include "eqtr4d.mm"

theorem scutun12
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A <<s B /\ C <<s { ( A |s B ) } /\ { ( A |s B ) } <<s D ) -> ( ( A u. C ) |s ( B u. D ) ) = ( A |s B ) )

  proof
    cA
    cB
    csslt
    wbr
    #
    cC
    cA
    cB
    cscut
    co
    #
    csn
    #
    csslt
    wbr
    #
    @2
    cD
    csslt
    wbr
    #
    w3a
    #
    cA
    cC
    cun
    #
    cB
    cD
    cun
    #
    cscut
    co
    #
    vx
    cv
    #
    cbday
    cfv
    #
    cbday
    @6
    vy
    cv
    #
    csn
    #
    csslt
    wbr
    #
    @12
    @7
    csslt
    wbr
    #
    wa
    #
    vy
    csur
    crab
    #
    cima
    #
    cint
    #
    wceq
    #
    vx
    @16
    crio
    #
    @1
    @5
    @6
    @7
    csslt
    wbr
    #
    @8
    @20
    wceq
    @5
    @6
    @2
    csslt
    wbr
    #
    @2
    @7
    csslt
    wbr
    #
    @21
    @5
    cA
    @2
    csslt
    wbr
    #
    @3
    @22
    @5
    @1
    csur
    wcel
    #
    @24
    @2
    cB
    csslt
    wbr
    #
    @5
    @0
    @25
    @24
    @26
    w3a
    @0
    @3
    @4
    simp1
    cA
    cB
    scutcut
    syl
    #
    simp2d
    @0
    @3
    @4
    simp2
    cA
    cC
    @2
    ssltun1
    syl2anc
    #
    @5
    @26
    @4
    @23
    @5
    @25
    @24
    @26
    @27
    simp3d
    @0
    @3
    @4
    simp3
    @2
    cB
    cD
    ssltun2
    syl2anc
    #
    @22
    @23
    @2
    c0
    wne
    @21
    @1
    cA
    cB
    cscut
    ovex
    snnz
    @6
    @2
    @7
    sslttr
    mp3an3
    syl2anc
    #
    vx
    vy
    @6
    @7
    scutval
    syl
    @5
    @20
    @1
    @5
    @1
    cbday
    cfv
    #
    @18
    wceq
    #
    @20
    @1
    wceq
    #
    @5
    @31
    @18
    @5
    @31
    @9
    wss
    #
    vx
    @17
    wral
    @31
    @18
    wss
    @5
    @34
    vx
    @17
    @9
    @17
    wcel
    #
    @6
    vz
    cv
    #
    csn
    #
    csslt
    wbr
    #
    @37
    @7
    csslt
    wbr
    #
    wa
    #
    @36
    @9
    cbday
    wbr
    #
    wa
    #
    vz
    csur
    wrex
    #
    @5
    @34
    @35
    @41
    vz
    @16
    wrex
    @43
    vz
    @9
    cbday
    @16
    vx
    vex
    elima
    @15
    @40
    @41
    vz
    vy
    csur
    vy
    vz
    weq
    #
    @13
    @38
    @14
    @39
    @44
    @12
    @37
    @6
    csslt
    @11
    @36
    sneq
    #
    breq2d
    @44
    @12
    @37
    @7
    csslt
    @45
    breq1d
    anbi12d
    rexrab
    bitri
    @5
    @42
    @34
    vz
    csur
    @5
    @36
    csur
    wcel
    #
    wa
    #
    @40
    @41
    @34
    @47
    @40
    @41
    @34
    wi
    @47
    @40
    wa
    #
    @41
    @36
    cbday
    cfv
    #
    @9
    wceq
    #
    @34
    @48
    @46
    @50
    @41
    wb
    #
    @5
    @46
    @40
    simplr
    #
    cbday
    csur
    wfn
    #
    @46
    @51
    bdayfn
    csur
    @36
    @9
    cbday
    fnbrfvb
    mpan
    syl
    @48
    @31
    @49
    wss
    #
    @50
    @34
    wi
    @48
    @31
    cbday
    cA
    @12
    csslt
    wbr
    #
    @12
    cB
    csslt
    wbr
    #
    wa
    #
    vy
    csur
    crab
    #
    cima
    #
    cint
    #
    @49
    @48
    @0
    @31
    @60
    wceq
    @0
    @3
    @4
    @46
    @40
    simpll1
    vy
    cA
    cB
    scutbday
    syl
    @48
    @49
    @59
    wcel
    #
    @60
    @49
    wss
    @48
    @36
    @58
    wcel
    #
    @61
    @48
    @46
    cA
    @37
    csslt
    wbr
    #
    @37
    cB
    csslt
    wbr
    #
    wa
    #
    @62
    @52
    @48
    @63
    @64
    @48
    @38
    @63
    @47
    @38
    @39
    simprl
    @38
    cA
    @6
    wss
    @63
    cA
    cC
    ssun1
    @6
    @37
    cA
    sssslt1
    mpan2
    syl
    @48
    @39
    @64
    @47
    @38
    @39
    simprr
    @39
    cB
    @7
    wss
    @64
    cB
    cD
    ssun1
    @37
    @7
    cB
    sssslt2
    mpan2
    syl
    jca
    @57
    @65
    vy
    @36
    csur
    @44
    @55
    @63
    @56
    @64
    @44
    @12
    @37
    cA
    csslt
    @45
    breq2d
    @44
    @12
    @37
    cB
    csslt
    @45
    breq1d
    anbi12d
    elrab
    sylanbrc
    @53
    @58
    csur
    wss
    @62
    @61
    bdayfn
    @57
    vy
    csur
    ssrab2
    csur
    @58
    cbday
    @36
    fnfvima
    mp3an12
    syl
    @49
    @59
    intss1
    syl
    eqsstrd
    @50
    @54
    @34
    @50
    @54
    @34
    @49
    @9
    @31
    sseq2
    biimpd
    com12
    syl
    sylbird
    ex
    impd
    rexlimdva
    syl5bi
    ralrimiv
    vx
    @31
    @17
    ssint
    sylibr
    @5
    @31
    @17
    wcel
    #
    @18
    @31
    wss
    @5
    @1
    @16
    wcel
    #
    @66
    @5
    @25
    @22
    @23
    wa
    #
    @67
    @5
    @25
    @24
    @26
    @27
    simp1d
    @5
    @22
    @23
    @28
    @29
    jca
    @15
    @68
    vy
    @1
    csur
    @11
    @1
    wceq
    #
    @13
    @22
    @14
    @23
    @69
    @12
    @2
    @6
    csslt
    @11
    @1
    sneq
    #
    breq2d
    @69
    @12
    @2
    @7
    csslt
    @70
    breq1d
    anbi12d
    elrab
    sylanbrc
    #
    @53
    @16
    csur
    wss
    @67
    @66
    bdayfn
    @15
    vy
    csur
    ssrab2
    csur
    @16
    cbday
    @1
    fnfvima
    mp3an12
    syl
    @31
    @17
    intss1
    syl
    eqssd
    @5
    @67
    @19
    vx
    @16
    wreu
    #
    @32
    @33
    wb
    @71
    @5
    @21
    @72
    @30
    vx
    vy
    @6
    @7
    conway
    syl
    @19
    @32
    vx
    @16
    @1
    @9
    @1
    wceq
    @10
    @31
    @18
    @9
    @1
    cbday
    fveq2
    eqeq1d
    riota2
    syl2anc
    mpbid
    eqcomd
    eqtr4d
end
