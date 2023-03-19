include "cv.mm"
include "wcel.mm"
include "cfn.mm"
include "cn.mm"
include "cz.mm"
include "csn.mm"
include "cun.mm"
include "wral.mm"
include "w3a.mm"
include "csu.mm"
include "cmo.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wss.mm"
include "snssi.mm"
include "ssequn1.mm"
include "wb.mm"
include "uncom.mm"
include "eqeq1i.mm"
include "sumeq1.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "eqcoms.mm"
include "sylbi.mm"
include "biimpd.mm"
include "a1d.mm"
include "syl.mm"
include "wn.mm"
include "wnel.mm"
include "df-nel.mm"
include "wa.mm"
include "csb.mm"
include "caddc.mm"
include "cvv.mm"
include "simp1.mm"
include "ad2antlr.mm"
include "simpl.mm"
include "adantr.mm"
include "vex.mm"
include "jctil.mm"
include "simplr3.mm"
include "fsumsplitsnun.mm"
include "syl3anc.mm"
include "cr.mm"
include "crp.mm"
include "ralunb.mm"
include "fsumzcl2.mm"
include "sylan2.mm"
include "3adant2.mm"
include "adantl.mm"
include "zred.mm"
include "modfsummodslem1.mm"
include "3ad2ant3.mm"
include "nnrp.mm"
include "3ad2ant2.mm"
include "modaddabs.mm"
include "eqcomd.mm"
include "simpr.mm"
include "jca.mm"
include "modabs2.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "zmodcl.mm"
include "nn0zd.mm"
include "expcom.mm"
include "ralimdv.mm"
include "com12.mm"
include "impcom.mm"
include "3adant1.mm"
include "cn0.mm"
include "anim1i.mm"
include "ancoms.mm"
include "nn0red.mm"
include "imp.mm"
include "csbov1g.mm"
include "mp1i.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "exp31.mm"
include "sylbir.mm"
include "pm2.61i.mm"

theorem modfsummods
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cN: class N

  disjoint A k
  disjoint N k
  disjoint k z
  assert |- ( ( A e. Fin /\ N e. NN /\ A. k e. ( A u. { z } ) B e. ZZ ) -> ( ( sum_ k e. A B mod N ) = ( sum_ k e. A ( B mod N ) mod N ) -> ( sum_ k e. ( A u. { z } ) B mod N ) = ( sum_ k e. ( A u. { z } ) ( B mod N ) mod N ) ) )

  proof
    vz
    cv
    #
    cA
    wcel
    #
    cA
    cfn
    wcel
    #
    cN
    cn
    wcel
    #
    cB
    cz
    wcel
    #
    vk
    cA
    @0
    csn
    #
    cun
    #
    wral
    #
    w3a
    #
    cA
    cB
    vk
    csu
    #
    cN
    cmo
    co
    #
    cA
    cB
    cN
    cmo
    co
    #
    vk
    csu
    #
    cN
    cmo
    co
    #
    wceq
    #
    @6
    cB
    vk
    csu
    #
    cN
    cmo
    co
    #
    @6
    @11
    vk
    csu
    #
    cN
    cmo
    co
    #
    wceq
    #
    wi
    #
    wi
    #
    @1
    @5
    cA
    wss
    #
    @21
    @0
    cA
    snssi
    @22
    @5
    cA
    cun
    #
    cA
    wceq
    #
    @21
    @5
    cA
    ssequn1
    @24
    @20
    @8
    @24
    @14
    @19
    @24
    @6
    cA
    wceq
    @14
    @19
    wb
    #
    @23
    @6
    cA
    @5
    cA
    uncom
    eqeq1i
    @25
    cA
    @6
    cA
    @6
    wceq
    #
    @10
    @16
    @13
    @18
    @26
    @9
    @15
    cN
    cmo
    cA
    @6
    cB
    vk
    sumeq1
    oveq1d
    @26
    @12
    @17
    cN
    cmo
    cA
    @6
    @11
    vk
    sumeq1
    oveq1d
    eqeq12d
    eqcoms
    sylbi
    biimpd
    a1d
    sylbi
    syl
    @1
    wn
    @0
    cA
    wnel
    #
    @21
    @0
    cA
    df-nel
    @27
    @8
    @14
    @19
    @27
    @8
    wa
    #
    @14
    wa
    #
    @16
    @9
    vk
    @0
    cB
    csb
    #
    caddc
    co
    #
    cN
    cmo
    co
    #
    @13
    @30
    cN
    cmo
    co
    #
    cN
    cmo
    co
    #
    caddc
    co
    #
    cN
    cmo
    co
    #
    @18
    @29
    @15
    @31
    cN
    cmo
    @29
    @2
    @0
    cvv
    wcel
    #
    @27
    wa
    #
    @7
    @15
    @31
    wceq
    @8
    @2
    @27
    @14
    @2
    @3
    @7
    simp1
    #
    ad2antlr
    #
    @29
    @27
    @37
    @28
    @27
    @14
    @27
    @8
    simpl
    adantr
    vz
    vex
    #
    jctil
    #
    @2
    @3
    @7
    @27
    @14
    simplr3
    cA
    cB
    vk
    cvv
    @0
    fsumsplitsnun
    syl3anc
    oveq1d
    @29
    @32
    @10
    @33
    caddc
    co
    #
    cN
    cmo
    co
    #
    @36
    @28
    @32
    @44
    wceq
    @14
    @28
    @44
    @32
    @28
    @9
    cr
    wcel
    @30
    cr
    wcel
    #
    cN
    crp
    wcel
    #
    @44
    @32
    wceq
    @28
    @9
    @8
    @9
    cz
    wcel
    #
    @27
    @2
    @7
    @47
    @3
    @7
    @2
    @4
    vk
    cA
    wral
    #
    @47
    @7
    @48
    @4
    vk
    @5
    wral
    #
    wa
    #
    @48
    @4
    vk
    cA
    @5
    ralunb
    #
    @48
    @49
    simpl
    sylbi
    cA
    cB
    vk
    fsumzcl2
    sylan2
    3adant2
    adantl
    zred
    @28
    @30
    @8
    @30
    cz
    wcel
    #
    @27
    @7
    @2
    @52
    @3
    vz
    cA
    cB
    vk
    modfsummodslem1
    #
    3ad2ant3
    adantl
    zred
    @8
    @46
    @27
    @3
    @2
    @46
    @7
    cN
    nnrp
    3ad2ant2
    #
    adantl
    #
    @9
    @30
    cN
    modaddabs
    syl3anc
    eqcomd
    adantr
    @29
    @43
    @35
    cN
    cmo
    @29
    @10
    @13
    @33
    @34
    caddc
    @28
    @14
    simpr
    @29
    @45
    @46
    wa
    #
    @33
    @34
    wceq
    @28
    @56
    @14
    @28
    @45
    @46
    @8
    @45
    @27
    @7
    @2
    @45
    @3
    @7
    @30
    @53
    zred
    3ad2ant3
    adantl
    @55
    jca
    adantr
    @56
    @34
    @33
    @30
    cN
    modabs2
    eqcomd
    syl
    oveq12d
    oveq1d
    eqtrd
    @29
    @36
    @12
    @33
    caddc
    co
    #
    cN
    cmo
    co
    #
    @18
    @29
    @12
    cr
    wcel
    #
    @33
    cr
    wcel
    #
    @46
    @36
    @58
    wceq
    @8
    @59
    @27
    @14
    @8
    @2
    @11
    cz
    wcel
    #
    vk
    cA
    wral
    #
    wa
    #
    @59
    @8
    @2
    @62
    @39
    @3
    @7
    @62
    @2
    @7
    @3
    @62
    @7
    @50
    @3
    @62
    wi
    #
    @51
    @48
    @64
    @49
    @3
    @48
    @62
    @3
    @4
    @61
    vk
    cA
    @4
    @3
    @61
    @4
    @3
    wa
    @11
    cB
    cN
    zmodcl
    nn0zd
    expcom
    #
    ralimdv
    com12
    adantr
    sylbi
    impcom
    3adant1
    jca
    @63
    @12
    cA
    @11
    vk
    fsumzcl2
    zred
    syl
    ad2antlr
    @8
    @60
    @27
    @14
    @3
    @7
    @60
    @2
    @3
    @7
    wa
    #
    @33
    @66
    @52
    @3
    wa
    #
    @33
    cn0
    wcel
    @7
    @3
    @67
    @7
    @52
    @3
    @53
    anim1i
    ancoms
    @30
    cN
    zmodcl
    syl
    nn0red
    3adant1
    ad2antlr
    @8
    @46
    @27
    @14
    @54
    ad2antlr
    @12
    @33
    cN
    modaddabs
    syl3anc
    @29
    @57
    @17
    cN
    cmo
    @29
    @17
    @57
    @29
    @17
    @12
    vk
    @0
    @11
    csb
    #
    caddc
    co
    #
    @57
    @29
    @2
    @38
    @61
    vk
    @6
    wral
    #
    @17
    @69
    wceq
    @40
    @42
    @8
    @70
    @27
    @14
    @3
    @7
    @70
    @2
    @3
    @7
    @70
    @3
    @4
    @61
    vk
    @6
    @65
    ralimdv
    imp
    3adant1
    ad2antlr
    cA
    @11
    vk
    cvv
    @0
    fsumsplitsnun
    syl3anc
    @29
    @68
    @33
    @12
    caddc
    @37
    @68
    @33
    wceq
    @29
    @41
    vk
    @0
    cB
    cN
    cmo
    cvv
    csbov1g
    mp1i
    oveq2d
    eqtrd
    eqcomd
    oveq1d
    eqtrd
    3eqtrd
    exp31
    sylbir
    pm2.61i
end
