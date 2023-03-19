include "cn.mm"
include "wcel.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "w3a.mm"
include "cmul.mm"
include "cmu.mm"
include "cfv.mm"
include "cc0.mm"
include "wa.mm"
include "cz.mm"
include "simpl2.mm"
include "mucl.mm"
include "syl.mm"
include "zcnd.mm"
include "mul02d.mm"
include "simpr.mm"
include "oveq1d.mm"
include "mumullem1.mm"
include "3adantl3.mm"
include "3eqtr4rd.mm"
include "simpl1.mm"
include "mul01d.mm"
include "oveq2d.mm"
include "cc.mm"
include "nncn.mm"
include "mulcom.mm"
include "syl2an.mm"
include "fveq2d.mm"
include "adantr.mm"
include "ancom1s.mm"
include "eqtrd.mm"
include "wne.mm"
include "cneg.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cprime.mm"
include "crab.mm"
include "chash.mm"
include "cexp.mm"
include "nnmulcld.mm"
include "mumullem2.mm"
include "muval2.mm"
include "syl2anc.mm"
include "caddc.mm"
include "neg1cn.mm"
include "a1i.mm"
include "cfn.mm"
include "cn0.mm"
include "cfz.mm"
include "wss.mm"
include "fzfi.mm"
include "prmnn.mm"
include "ssriv.mm"
include "rabss2.mm"
include "ax-mp.mm"
include "dvdsssfz1.mm"
include "syl5ss.mm"
include "ssfi.mm"
include "sylancr.mm"
include "hashcl.mm"
include "expaddd.mm"
include "cun.mm"
include "wo.mm"
include "wb.mm"
include "nnzd.mm"
include "adantlr.mm"
include "euclemma.mm"
include "syl3anc.mm"
include "rabbidva.mm"
include "unrab.mm"
include "syl6eqr.mm"
include "cin.mm"
include "c0.mm"
include "inrab.mm"
include "wn.mm"
include "wral.mm"
include "nprmdvds1.mm"
include "adantl.mm"
include "wi.mm"
include "prmz.mm"
include "dvdsgcd.mm"
include "simpll3.mm"
include "breq2d.mm"
include "sylibd.mm"
include "mtod.mm"
include "ralrimiva.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "syl5eq.mm"
include "hashun.mm"
include "simprl.mm"
include "simprr.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "pm2.61da2ne.mm"

theorem mumul
  let cA: class A
  let cB: class B
  let vp: setvar p


  assert |- ( ( A e. NN /\ B e. NN /\ ( A gcd B ) = 1 ) -> ( mmu ` ( A x. B ) ) = ( ( mmu ` A ) x. ( mmu ` B ) ) )

  proof
    cA
    cn
    wcel
    #
    cB
    cn
    wcel
    #
    cA
    cB
    cgcd
    co
    #
    c1
    wceq
    #
    w3a
    #
    cA
    cB
    cmul
    co
    #
    cmu
    cfv
    #
    cA
    cmu
    cfv
    #
    cB
    cmu
    cfv
    #
    cmul
    co
    #
    wceq
    @7
    cc0
    @8
    cc0
    @4
    @7
    cc0
    wceq
    #
    wa
    #
    cc0
    @8
    cmul
    co
    cc0
    @9
    @6
    @11
    @8
    @11
    @8
    @11
    @1
    @8
    cz
    wcel
    @0
    @1
    @3
    @10
    simpl2
    cB
    mucl
    syl
    zcnd
    mul02d
    @11
    @7
    cc0
    @8
    cmul
    @4
    @10
    simpr
    oveq1d
    @0
    @1
    @10
    @6
    cc0
    wceq
    #
    @3
    cA
    cB
    mumullem1
    3adantl3
    3eqtr4rd
    @4
    @8
    cc0
    wceq
    #
    wa
    #
    @7
    cc0
    cmul
    co
    cc0
    @9
    @6
    @14
    @7
    @14
    @7
    @14
    @0
    @7
    cz
    wcel
    @0
    @1
    @3
    @13
    simpl1
    cA
    mucl
    syl
    zcnd
    mul01d
    @14
    @8
    cc0
    @7
    cmul
    @4
    @13
    simpr
    oveq2d
    @0
    @1
    @13
    @12
    @3
    @0
    @1
    wa
    #
    @13
    wa
    @6
    cB
    cA
    cmul
    co
    #
    cmu
    cfv
    #
    cc0
    @15
    @6
    @17
    wceq
    @13
    @15
    @5
    @16
    cmu
    @0
    cA
    cc
    wcel
    cB
    cc
    wcel
    @5
    @16
    wceq
    @1
    cA
    nncn
    cB
    nncn
    cA
    cB
    mulcom
    syl2an
    fveq2d
    adantr
    @1
    @0
    @13
    @17
    cc0
    wceq
    cB
    cA
    mumullem1
    ancom1s
    eqtrd
    3adantl3
    3eqtr4rd
    @4
    @7
    cc0
    wne
    #
    @8
    cc0
    wne
    #
    wa
    #
    wa
    #
    @6
    c1
    cneg
    #
    vp
    cv
    #
    @5
    cdvds
    wbr
    #
    vp
    cprime
    crab
    #
    chash
    cfv
    #
    cexp
    co
    #
    @9
    @21
    @5
    cn
    wcel
    @6
    cc0
    wne
    @6
    @27
    wceq
    @21
    cA
    cB
    @0
    @1
    @3
    @20
    simpl1
    #
    @0
    @1
    @3
    @20
    simpl2
    #
    nnmulcld
    cA
    cB
    mumullem2
    @5
    vp
    muval2
    syl2anc
    @21
    @22
    @23
    cA
    cdvds
    wbr
    #
    vp
    cprime
    crab
    #
    chash
    cfv
    #
    @23
    cB
    cdvds
    wbr
    #
    vp
    cprime
    crab
    #
    chash
    cfv
    #
    caddc
    co
    #
    cexp
    co
    @22
    @32
    cexp
    co
    #
    @22
    @35
    cexp
    co
    #
    cmul
    co
    @27
    @9
    @21
    @22
    @32
    @35
    @22
    cc
    wcel
    @21
    neg1cn
    a1i
    @21
    @34
    cfn
    wcel
    #
    @35
    cn0
    wcel
    @21
    c1
    cB
    cfz
    co
    #
    cfn
    wcel
    @34
    @40
    wss
    @39
    c1
    cB
    fzfi
    @21
    @34
    @33
    vp
    cn
    crab
    #
    @40
    cprime
    cn
    wss
    #
    @34
    @41
    wss
    vp
    cprime
    cn
    @23
    prmnn
    ssriv
    #
    @33
    vp
    cprime
    cn
    rabss2
    ax-mp
    @21
    @1
    @41
    @40
    wss
    @29
    cB
    vp
    dvdsssfz1
    syl
    syl5ss
    @40
    @34
    ssfi
    sylancr
    #
    @34
    hashcl
    syl
    @21
    @31
    cfn
    wcel
    #
    @32
    cn0
    wcel
    @21
    c1
    cA
    cfz
    co
    #
    cfn
    wcel
    @31
    @46
    wss
    @45
    c1
    cA
    fzfi
    @21
    @31
    @30
    vp
    cn
    crab
    #
    @46
    @42
    @31
    @47
    wss
    @43
    @30
    vp
    cprime
    cn
    rabss2
    ax-mp
    @21
    @0
    @47
    @46
    wss
    @28
    cA
    vp
    dvdsssfz1
    syl
    syl5ss
    @46
    @31
    ssfi
    sylancr
    #
    @31
    hashcl
    syl
    expaddd
    @21
    @26
    @36
    @22
    cexp
    @21
    @26
    @31
    @34
    cun
    #
    chash
    cfv
    #
    @36
    @21
    @25
    @49
    chash
    @21
    @25
    @30
    @33
    wo
    #
    vp
    cprime
    crab
    @49
    @21
    @24
    @51
    vp
    cprime
    @21
    @23
    cprime
    wcel
    #
    wa
    #
    @52
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    @24
    @51
    wb
    @21
    @52
    simpr
    @4
    @52
    @54
    @20
    @4
    @52
    wa
    #
    cA
    @0
    @1
    @3
    @52
    simpl1
    nnzd
    adantlr
    #
    @4
    @52
    @55
    @20
    @56
    cB
    @0
    @1
    @3
    @52
    simpl2
    nnzd
    adantlr
    #
    @23
    cA
    cB
    euclemma
    syl3anc
    rabbidva
    @30
    @33
    vp
    cprime
    unrab
    syl6eqr
    fveq2d
    @21
    @45
    @39
    @31
    @34
    cin
    #
    c0
    wceq
    @50
    @36
    wceq
    @48
    @44
    @21
    @59
    @30
    @33
    wa
    #
    vp
    cprime
    crab
    #
    c0
    @30
    @33
    vp
    cprime
    inrab
    @21
    @60
    wn
    #
    vp
    cprime
    wral
    @61
    c0
    wceq
    @21
    @62
    vp
    cprime
    @53
    @60
    @23
    c1
    cdvds
    wbr
    #
    @52
    @63
    wn
    @21
    @23
    nprmdvds1
    adantl
    @53
    @60
    @23
    @2
    cdvds
    wbr
    #
    @63
    @53
    @23
    cz
    wcel
    #
    @54
    @55
    @60
    @64
    wi
    @52
    @65
    @21
    @23
    prmz
    adantl
    @57
    @58
    @23
    cA
    cB
    dvdsgcd
    syl3anc
    @53
    @2
    c1
    @23
    cdvds
    @0
    @1
    @3
    @20
    @52
    simpll3
    breq2d
    sylibd
    mtod
    ralrimiva
    @60
    vp
    cprime
    rabeq0
    sylibr
    syl5eq
    @31
    @34
    hashun
    syl3anc
    eqtrd
    oveq2d
    @21
    @7
    @37
    @8
    @38
    cmul
    @21
    @0
    @18
    @7
    @37
    wceq
    @28
    @4
    @18
    @19
    simprl
    cA
    vp
    muval2
    syl2anc
    @21
    @1
    @19
    @8
    @38
    wceq
    @29
    @4
    @18
    @19
    simprr
    cB
    vp
    muval2
    syl2anc
    oveq12d
    3eqtr4rd
    eqtr4d
    pm2.61da2ne
end
