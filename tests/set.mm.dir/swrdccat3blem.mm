include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "cop.mm"
include "csubstr.mm"
include "cconcat.mm"
include "cif.mm"
include "wceq.mm"
include "wi.mm"
include "cn0.mm"
include "lencl.mm"
include "nn0le0eq0.mm"
include "biimpd.mm"
include "syl.mm"
include "adantl.mm"
include "c0.mm"
include "hasheq0.mm"
include "imp.mm"
include "eqcomi.mm"
include "eleq1i.mm"
include "cr.mm"
include "nn0re.mm"
include "w3a.mm"
include "elfz2nn0.mm"
include "recn.mm"
include "addid1d.mm"
include "breq2d.mm"
include "wb.mm"
include "anim1i.mm"
include "ancoms.mm"
include "letri3.mm"
include "biimprd.mm"
include "exp4b.mm"
include "com23.mm"
include "sylbid.mm"
include "com3l.mm"
include "impcom.mm"
include "3adant2.mm"
include "com12.mm"
include "syl5bi.mm"
include "sylbi.mm"
include "elfznn0.mm"
include "swrd00.mm"
include "eqtr4i.mm"
include "nn0cn.mm"
include "subidd.mm"
include "opeq1d.mm"
include "oveq2d.mm"
include "opeq2d.mm"
include "3eqtr4a.mm"
include "a1i.mm"
include "eleq1.mm"
include "oveq1.mm"
include "opeq1.mm"
include "eqeq12d.mm"
include "3imtr4d.mm"
include "a1d.mm"
include "syld.mm"
include "wn.mm"
include "swrdcl.mm"
include "ccatrid.mm"
include "cc.mm"
include "addid1.mm"
include "eqcomd.mm"
include "eqtrd.mm"
include "adantr.mm"
include "ifeqda.mm"
include "ex.mm"
include "ad3antrrr.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "simpr.mm"
include "opeq2.mm"
include "oveq12d.mm"
include "ifeq12d.mm"
include "imbi12d.mm"
include "adantll.mm"
include "mpbird.mm"
include "mpdan.mm"
include "sylbir.mm"
include "nn0red.mm"
include "leaddle0.mm"
include "syl2an.mm"
include "pm2.24.mm"
include "syl6bi.mm"
include "pm2.61d.mm"

theorem swrdccat3blem
  let cA: class A
  let cB: class B
  let cL: class L
  let cM: class M
  let cV: class V
  let vk: setvar k
  let cN: class N
  assume swrdccatin12.l: |- L = ( # ` A )


  assert |- ( ( ( ( A e. Word V /\ B e. Word V ) /\ M e. ( 0 ... ( L + ( # ` B ) ) ) ) /\ ( L + ( # ` B ) ) <_ L ) -> if ( L <_ M , ( B substr <. ( M - L ) , ( # ` B ) >. ) , ( ( A substr <. M , L >. ) ++ B ) ) = ( A substr <. M , ( L + ( # ` B ) ) >. ) )

  proof
    cA
    cV
    cword
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cM
    cc0
    cL
    cB
    chash
    cfv
    #
    caddc
    co
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    @5
    cL
    cle
    wbr
    #
    wa
    @4
    cc0
    cle
    wbr
    #
    cL
    cM
    cle
    wbr
    #
    cB
    cM
    cL
    cmin
    co
    #
    @4
    cop
    #
    csubstr
    co
    #
    cA
    cM
    cL
    cop
    #
    csubstr
    co
    #
    cB
    cconcat
    co
    #
    cif
    #
    cA
    cM
    @5
    cop
    #
    csubstr
    co
    #
    wceq
    #
    @8
    @10
    @21
    wi
    #
    @9
    @3
    @7
    @22
    @3
    @10
    @7
    @21
    @3
    @10
    @4
    cc0
    wceq
    #
    @7
    @21
    wi
    #
    @2
    @10
    @23
    wi
    #
    @1
    @2
    @4
    cn0
    wcel
    #
    @25
    cV
    cB
    lencl
    #
    @26
    @10
    @23
    @4
    nn0le0eq0
    biimpd
    syl
    adantl
    @3
    @23
    @24
    @3
    @23
    wa
    #
    cB
    c0
    wceq
    #
    @24
    @3
    @23
    @29
    @2
    @23
    @29
    wi
    @1
    @2
    @23
    @29
    cB
    @0
    hasheq0
    biimpd
    adantl
    imp
    @28
    @29
    wa
    @24
    cM
    cc0
    cL
    cc0
    caddc
    co
    #
    cfz
    co
    #
    wcel
    #
    @11
    c0
    @12
    cc0
    cop
    #
    csubstr
    co
    #
    @16
    c0
    cconcat
    co
    #
    cif
    #
    cA
    cM
    @30
    cop
    #
    csubstr
    co
    #
    wceq
    #
    wi
    #
    @1
    @40
    @2
    @23
    @29
    @1
    @32
    @39
    @1
    @32
    wa
    #
    @11
    @34
    @35
    @38
    @41
    @11
    @34
    @38
    wceq
    #
    @41
    @11
    cM
    cL
    wceq
    #
    @42
    @1
    @32
    @11
    @43
    wi
    #
    @1
    cA
    chash
    cfv
    #
    cn0
    wcel
    #
    @32
    @44
    wi
    #
    cV
    cA
    lencl
    #
    @46
    cL
    cn0
    wcel
    #
    @47
    @45
    cL
    cn0
    cL
    @45
    swrdccatin12.l
    eqcomi
    eleq1i
    #
    @49
    cL
    cr
    wcel
    #
    @47
    cL
    nn0re
    #
    @32
    cM
    cn0
    wcel
    #
    @30
    cn0
    wcel
    #
    cM
    @30
    cle
    wbr
    #
    w3a
    #
    @51
    @44
    cM
    @30
    elfz2nn0
    @56
    @51
    @44
    @53
    @55
    @51
    @44
    wi
    #
    @54
    @55
    @53
    @57
    @51
    @55
    @53
    @44
    @51
    @55
    cM
    cL
    cle
    wbr
    #
    @53
    @44
    wi
    @51
    @30
    cL
    cM
    cle
    @51
    cL
    cL
    recn
    addid1d
    breq2d
    @51
    @53
    @58
    @44
    @51
    @53
    @58
    @11
    @43
    @51
    @53
    wa
    #
    @43
    @58
    @11
    wa
    #
    @59
    cM
    cr
    wcel
    #
    @51
    wa
    #
    @43
    @60
    wb
    @53
    @51
    @62
    @53
    @61
    @51
    cM
    nn0re
    anim1i
    ancoms
    cM
    cL
    letri3
    syl
    biimprd
    exp4b
    com23
    sylbid
    com3l
    impcom
    3adant2
    com12
    syl5bi
    syl
    sylbi
    syl
    imp
    @32
    @1
    @43
    @42
    wi
    #
    @32
    @53
    @1
    @63
    wi
    cM
    @30
    elfznn0
    @53
    @63
    @1
    @43
    @53
    @42
    @43
    @49
    c0
    cL
    cL
    cmin
    co
    #
    cc0
    cop
    #
    csubstr
    co
    #
    cA
    cL
    @30
    cop
    #
    csubstr
    co
    #
    wceq
    #
    @53
    @42
    @49
    @69
    wi
    @43
    @49
    c0
    cc0
    cc0
    cop
    #
    csubstr
    co
    #
    cA
    cL
    cL
    cop
    #
    csubstr
    co
    #
    @66
    @68
    @71
    c0
    @73
    c0
    cc0
    swrd00
    cA
    cL
    swrd00
    eqtr4i
    @49
    @65
    @70
    c0
    csubstr
    @49
    @64
    cc0
    cc0
    @49
    cL
    cL
    nn0cn
    #
    subidd
    opeq1d
    oveq2d
    @49
    @67
    @72
    cA
    csubstr
    @49
    @30
    cL
    cL
    @49
    cL
    @74
    addid1d
    opeq2d
    oveq2d
    3eqtr4a
    a1i
    cM
    cL
    cn0
    eleq1
    @43
    @34
    @66
    @38
    @68
    @43
    @33
    @65
    c0
    csubstr
    @43
    @12
    @64
    cc0
    cM
    cL
    cL
    cmin
    oveq1
    opeq1d
    oveq2d
    @43
    @37
    @67
    cA
    csubstr
    cM
    cL
    @30
    opeq1
    oveq2d
    eqeq12d
    3imtr4d
    com12
    a1d
    syl
    impcom
    syld
    imp
    @41
    @35
    @38
    wceq
    #
    @11
    wn
    @1
    @75
    @32
    @1
    @35
    @16
    @38
    @1
    @16
    @0
    wcel
    @35
    @16
    wceq
    cV
    cA
    cM
    cL
    swrdcl
    cV
    @16
    ccatrid
    syl
    @1
    @15
    @37
    cA
    csubstr
    @1
    cL
    @30
    cM
    @1
    cL
    cc
    wcel
    #
    cL
    @30
    wceq
    @1
    @46
    @76
    @48
    @46
    @49
    @76
    @50
    @74
    sylbi
    syl
    @76
    @30
    cL
    cL
    addid1
    eqcomd
    syl
    opeq2d
    oveq2d
    eqtrd
    adantr
    adantr
    ifeqda
    ex
    ad3antrrr
    @23
    @29
    @24
    @40
    wb
    @3
    @23
    @29
    wa
    #
    @7
    @32
    @21
    @39
    @23
    @7
    @32
    wb
    @29
    @23
    @6
    @31
    cM
    @23
    @5
    @30
    cc0
    cfz
    @4
    cc0
    cL
    caddc
    oveq2
    #
    oveq2d
    eleq2d
    adantr
    @77
    @18
    @36
    @20
    @38
    @77
    @11
    @14
    @34
    @17
    @35
    @77
    cB
    c0
    @13
    @33
    csubstr
    @23
    @29
    simpr
    @23
    @13
    @33
    wceq
    @29
    @4
    cc0
    @12
    opeq2
    adantr
    oveq12d
    @29
    @17
    @35
    wceq
    @23
    cB
    c0
    @16
    cconcat
    oveq2
    adantl
    ifeq12d
    @23
    @20
    @38
    wceq
    @29
    @23
    @19
    @37
    cA
    csubstr
    @23
    @5
    @30
    cM
    @78
    opeq2d
    oveq2d
    adantr
    eqeq12d
    imbi12d
    adantll
    mpbird
    mpdan
    ex
    syld
    com23
    imp
    adantr
    @8
    @9
    @10
    wn
    @21
    wi
    #
    @3
    @9
    @79
    wi
    @7
    @3
    @9
    @10
    @79
    @1
    @51
    @4
    cr
    wcel
    @9
    @10
    wb
    @2
    @1
    @46
    @51
    @48
    @46
    @49
    @51
    cL
    @45
    cn0
    swrdccatin12.l
    eleq1i
    @52
    sylbir
    syl
    @2
    @4
    @27
    nn0red
    cL
    @4
    leaddle0
    syl2an
    @10
    @21
    pm2.24
    syl6bi
    adantr
    imp
    pm2.61d
end
