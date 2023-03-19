include "cv.mm"
include "com.mm"
include "wcel.mm"
include "cfv.mm"
include "cpw.mm"
include "cen.mm"
include "wbr.mm"
include "csuc.mm"
include "wral.mm"
include "ciun.mm"
include "csdm.mm"
include "wi.mm"
include "c0.mm"
include "wceq.mm"
include "suceq.mm"
include "raleqdv.mm"
include "iuneq1.mm"
include "fveq2.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "0iun.mm"
include "0ex.mm"
include "sucid.mm"
include "pweq.mm"
include "rspcv.mm"
include "ax-mp.mm"
include "canth2.mm"
include "ensym.mm"
include "sdomentr.mm"
include "sylancr.mm"
include "syl.mm"
include "syl5eqbr.mm"
include "wa.mm"
include "wss.mm"
include "sssucid.mm"
include "ssralv.mm"
include "pm2.27.mm"
include "adantl.mm"
include "ccda.mm"
include "co.mm"
include "vex.mm"
include "elelsuc.mm"
include "mp2b.mm"
include "cdaen.mm"
include "syl2anc.mm"
include "c1o.mm"
include "pwcda1.mm"
include "wn.mm"
include "word.mm"
include "nnord.mm"
include "ordirr.mm"
include "cda1en.mm"
include "mpdan.mm"
include "pwen.mm"
include "entr.mm"
include "syl2an.mm"
include "sucex.mm"
include "ensymd.mm"
include "adantr.mm"
include "ancoms.mm"
include "cfn.mm"
include "nnfi.mm"
include "pwfi.mm"
include "isfinite.mm"
include "bitri.mm"
include "sylib.mm"
include "ensdomtr.mm"
include "sylibr.mm"
include "cdom.mm"
include "cun.mm"
include "iunsuc.mm"
include "cvv.mm"
include "fvex.mm"
include "iunex.mm"
include "uncdadom.mm"
include "mp2an.mm"
include "eqbrtri.mm"
include "ccrd.mm"
include "coa.mm"
include "cdm.mm"
include "sdomtr.mm"
include "sylan2b.mm"
include "finnum.mm"
include "cardacda.mm"
include "ficardom.mm"
include "cardid2.mm"
include "3syl.mm"
include "simpl.mm"
include "sylan.mm"
include "syl21anc.mm"
include "con0.mm"
include "wb.mm"
include "cardon.mm"
include "onenon.mm"
include "cardsdomel.mm"
include "cardidm.mm"
include "eleq2i.mm"
include "w3a.mm"
include "nnaordr.mm"
include "biimpa.mm"
include "syl31anc.mm"
include "nnacl.mm"
include "cardnn.mm"
include "eleqtrrd.mm"
include "cardsdomelir.mm"
include "domsdomtr.mm"
include "expcom.mm"
include "sylsyld.mm"
include "syld.mm"
include "ex.mm"
include "com23.mm"
include "finds1.mm"
include "imp.mm"

theorem pwsdompw
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let vm: setvar m

  disjoint B k
  disjoint B n
  disjoint k n
  disjoint B m
  disjoint k m
  disjoint m n
  assert |- ( ( n e. _om /\ A. k e. suc n ( B ` k ) ~~ ~P k ) -> U_ k e. n ( B ` k ) ~< ( B ` n ) )

  proof
    vn
    cv
    #
    com
    wcel
    vk
    cv
    #
    cB
    cfv
    #
    @1
    cpw
    #
    cen
    wbr
    #
    vk
    @0
    csuc
    #
    wral
    #
    vk
    @0
    @2
    ciun
    #
    @0
    cB
    cfv
    #
    csdm
    wbr
    #
    @6
    @9
    wi
    @4
    vk
    c0
    csuc
    #
    wral
    #
    vk
    c0
    @2
    ciun
    #
    c0
    cB
    cfv
    #
    csdm
    wbr
    #
    wi
    @4
    vk
    vm
    cv
    #
    csuc
    #
    wral
    #
    vk
    @15
    @2
    ciun
    #
    @15
    cB
    cfv
    #
    csdm
    wbr
    #
    wi
    #
    @4
    vk
    @16
    csuc
    #
    wral
    #
    vk
    @16
    @2
    ciun
    #
    @16
    cB
    cfv
    #
    csdm
    wbr
    #
    wi
    vn
    vm
    @0
    c0
    wceq
    #
    @6
    @11
    @9
    @14
    @27
    @4
    vk
    @5
    @10
    @0
    c0
    suceq
    raleqdv
    @27
    @7
    @12
    @8
    @13
    csdm
    vk
    @0
    c0
    @2
    iuneq1
    @0
    c0
    cB
    fveq2
    breq12d
    imbi12d
    @0
    @15
    wceq
    #
    @6
    @17
    @9
    @20
    @28
    @4
    vk
    @5
    @16
    @0
    @15
    suceq
    raleqdv
    @28
    @7
    @18
    @8
    @19
    csdm
    vk
    @0
    @15
    @2
    iuneq1
    @0
    @15
    cB
    fveq2
    breq12d
    imbi12d
    @0
    @16
    wceq
    #
    @6
    @23
    @9
    @26
    @29
    @4
    vk
    @5
    @22
    @0
    @16
    suceq
    raleqdv
    @29
    @7
    @24
    @8
    @25
    csdm
    vk
    @0
    @16
    @2
    iuneq1
    @0
    @16
    cB
    fveq2
    breq12d
    imbi12d
    @11
    @12
    c0
    @13
    csdm
    vk
    @2
    0iun
    @11
    @13
    c0
    cpw
    #
    cen
    wbr
    #
    c0
    @13
    csdm
    wbr
    #
    c0
    @10
    wcel
    @11
    @31
    wi
    c0
    0ex
    sucid
    @4
    @31
    vk
    c0
    @10
    @1
    c0
    wceq
    @2
    @13
    @3
    @30
    cen
    @1
    c0
    cB
    fveq2
    @1
    c0
    pweq
    breq12d
    rspcv
    ax-mp
    @31
    c0
    @30
    csdm
    wbr
    @30
    @13
    cen
    wbr
    @32
    c0
    0ex
    canth2
    @13
    @30
    ensym
    c0
    @30
    @13
    sdomentr
    sylancr
    syl
    syl5eqbr
    @15
    com
    wcel
    #
    @23
    @21
    @26
    @33
    @23
    @21
    @26
    wi
    @33
    @23
    wa
    #
    @21
    @20
    @26
    @23
    @21
    @20
    wi
    #
    @33
    @23
    @17
    @35
    @16
    @22
    wss
    @23
    @17
    wi
    @16
    sssucid
    @4
    vk
    @16
    @22
    ssralv
    ax-mp
    @17
    @20
    pm2.27
    syl
    adantl
    @34
    @19
    @19
    ccda
    co
    #
    @25
    cen
    wbr
    #
    @20
    @24
    @36
    csdm
    wbr
    #
    @26
    @23
    @33
    @37
    @23
    @33
    wa
    #
    @36
    @16
    cpw
    #
    cen
    wbr
    #
    @40
    @25
    cen
    wbr
    #
    @37
    @23
    @36
    @15
    cpw
    #
    @43
    ccda
    co
    #
    cen
    wbr
    #
    @44
    @40
    cen
    wbr
    #
    @41
    @33
    @23
    @19
    @43
    cen
    wbr
    #
    @47
    @45
    @15
    @16
    wcel
    @15
    @22
    wcel
    @23
    @47
    wi
    @15
    vm
    vex
    #
    sucid
    @15
    @16
    elelsuc
    @4
    @47
    vk
    @15
    @22
    @1
    @15
    wceq
    @2
    @19
    @3
    @43
    cen
    @1
    @15
    cB
    fveq2
    #
    @1
    @15
    pweq
    breq12d
    rspcv
    mp2b
    #
    @50
    @19
    @43
    @19
    @43
    cdaen
    syl2anc
    @33
    @44
    @15
    c1o
    ccda
    co
    #
    cpw
    #
    cen
    wbr
    @52
    @40
    cen
    wbr
    #
    @46
    @15
    com
    pwcda1
    @33
    @51
    @16
    cen
    wbr
    #
    @53
    @33
    @15
    @15
    wcel
    wn
    #
    @54
    @33
    @15
    word
    @55
    @15
    nnord
    @15
    ordirr
    syl
    @15
    com
    cda1en
    mpdan
    @51
    @16
    pwen
    syl
    @44
    @52
    @40
    entr
    syl2anc
    @36
    @44
    @40
    entr
    syl2an
    @23
    @42
    @33
    @23
    @25
    @40
    @16
    @22
    wcel
    @23
    @25
    @40
    cen
    wbr
    #
    wi
    @16
    @15
    @48
    sucex
    sucid
    @4
    @56
    vk
    @16
    @22
    @1
    @16
    wceq
    @2
    @25
    @3
    @40
    cen
    @1
    @16
    cB
    fveq2
    @1
    @16
    pweq
    breq12d
    rspcv
    ax-mp
    ensymd
    adantr
    @36
    @40
    @25
    entr
    syl2anc
    ancoms
    @34
    @19
    cfn
    wcel
    #
    @20
    @38
    wi
    @23
    @33
    @57
    @39
    @19
    com
    csdm
    wbr
    #
    @57
    @23
    @47
    @43
    com
    csdm
    wbr
    #
    @58
    @33
    @50
    @33
    @15
    cfn
    wcel
    #
    @59
    @15
    nnfi
    @60
    @43
    cfn
    wcel
    @59
    @15
    pwfi
    @43
    isfinite
    bitri
    sylib
    @19
    @43
    com
    ensdomtr
    syl2an
    @19
    isfinite
    #
    sylibr
    ancoms
    @20
    @57
    @38
    @20
    @57
    wa
    #
    @24
    @18
    @19
    ccda
    co
    #
    cdom
    wbr
    @63
    @36
    csdm
    wbr
    #
    @38
    @24
    @18
    @19
    cun
    #
    @63
    cdom
    vk
    @15
    @2
    @19
    @48
    @49
    iunsuc
    @18
    cvv
    wcel
    @19
    cvv
    wcel
    @65
    @63
    cdom
    wbr
    vk
    @15
    @2
    @48
    @1
    cB
    fvex
    iunex
    @15
    cB
    fvex
    @18
    @19
    cvv
    cvv
    uncdadom
    mp2an
    eqbrtri
    @62
    @63
    @19
    ccrd
    cfv
    #
    @66
    coa
    co
    #
    csdm
    wbr
    #
    @67
    @36
    cen
    wbr
    #
    @64
    @62
    @63
    @18
    ccrd
    cfv
    #
    @66
    coa
    co
    #
    cen
    wbr
    #
    @71
    @67
    csdm
    wbr
    #
    @68
    @62
    @18
    ccrd
    cdm
    #
    wcel
    #
    @19
    @74
    wcel
    #
    @72
    @62
    @18
    cfn
    wcel
    #
    @75
    @62
    @18
    com
    csdm
    wbr
    #
    @77
    @57
    @20
    @58
    @78
    @61
    @18
    @19
    com
    sdomtr
    sylan2b
    @18
    isfinite
    sylibr
    #
    @18
    finnum
    #
    syl
    @57
    @76
    @20
    @19
    finnum
    #
    adantl
    @18
    @19
    cardacda
    syl2anc
    @62
    @71
    @67
    ccrd
    cfv
    #
    wcel
    @73
    @62
    @71
    @67
    @82
    @62
    @70
    com
    wcel
    #
    @66
    com
    wcel
    #
    @84
    @70
    @66
    wcel
    #
    @71
    @67
    wcel
    #
    @62
    @77
    @83
    @79
    @18
    ficardom
    syl
    @57
    @84
    @20
    @19
    ficardom
    #
    adantl
    #
    @88
    @62
    @70
    @66
    csdm
    wbr
    #
    @85
    @62
    @70
    @18
    cen
    wbr
    #
    @20
    @19
    @66
    cen
    wbr
    #
    @89
    @62
    @77
    @75
    @90
    @79
    @80
    @18
    cardid2
    3syl
    @20
    @57
    simpl
    @57
    @91
    @20
    @57
    @76
    @66
    @19
    cen
    wbr
    @91
    @81
    @19
    cardid2
    @66
    @19
    ensym
    3syl
    adantl
    @90
    @20
    wa
    @70
    @19
    csdm
    wbr
    @91
    @89
    @70
    @18
    @19
    ensdomtr
    @70
    @19
    @66
    sdomentr
    sylan
    syl21anc
    @89
    @70
    @66
    ccrd
    cfv
    #
    wcel
    #
    @85
    @70
    con0
    wcel
    @66
    @74
    wcel
    #
    @89
    @93
    wb
    @18
    cardon
    @66
    con0
    wcel
    @94
    @19
    cardon
    @66
    onenon
    ax-mp
    @70
    @66
    cardsdomel
    mp2an
    @92
    @66
    @70
    @19
    cardidm
    eleq2i
    bitri
    sylib
    @83
    @84
    @84
    w3a
    @85
    @86
    @70
    @66
    @66
    nnaordr
    biimpa
    syl31anc
    @57
    @82
    @67
    wceq
    #
    @20
    @57
    @67
    com
    wcel
    #
    @95
    @57
    @84
    @84
    @96
    @87
    @87
    @66
    @66
    nnacl
    syl2anc
    @67
    cardnn
    syl
    adantl
    eleqtrrd
    @71
    @67
    cardsdomelir
    syl
    @63
    @71
    @67
    ensdomtr
    syl2anc
    @57
    @69
    @20
    @57
    @36
    @67
    @57
    @76
    @76
    @36
    @67
    cen
    wbr
    @81
    @81
    @19
    @19
    cardacda
    syl2anc
    ensymd
    adantl
    @63
    @67
    @36
    sdomentr
    syl2anc
    @24
    @63
    @36
    domsdomtr
    sylancr
    expcom
    syl
    @38
    @37
    @26
    @24
    @36
    @25
    sdomentr
    expcom
    sylsyld
    syld
    ex
    com23
    finds1
    imp
end
