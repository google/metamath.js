include "cpi.mm"
include "cneg.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "ccos.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "csqrt.mm"
include "cr.mm"
include "wss.mm"
include "pire.mm"
include "renegcli.mm"
include "iccssre.mm"
include "mp2an.mm"
include "sseli.mm"
include "rehalfcld.mm"
include "recoscld.mm"
include "1re.mm"
include "readdcl.mm"
include "sylancr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cosbnd.mm"
include "simpld.mm"
include "wb.mm"
include "recoscl.mm"
include "wa.mm"
include "cmin.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "subneg.mm"
include "addcom.mm"
include "ancoms.mm"
include "eqtr4d.mm"
include "syl2an.mm"
include "breq2d.mm"
include "renegcl.mm"
include "subge0.mm"
include "sylan2.mm"
include "halfnneg2.mm"
include "syl.mm"
include "3bitr3d.mm"
include "sylancl.mm"
include "mpbid.mm"
include "resqrtcld.mm"
include "w3a.mm"
include "elicc2i.mm"
include "clt.mm"
include "2re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "lediv1.mm"
include "mp3an13.mm"
include "wne.mm"
include "picn.mm"
include "2cn.mm"
include "2ne0.mm"
include "divneg.mm"
include "mp3an.mm"
include "breq1i.mm"
include "syl6bbr.mm"
include "mp3an23.mm"
include "anbi12d.mm"
include "cxr.mm"
include "rehalfcl.mm"
include "rexrd.mm"
include "halfpire.mm"
include "rexri.mm"
include "elicc4.mm"
include "mp3an12.mm"
include "bitr4d.mm"
include "biimpd.mm"
include "3impib.mm"
include "sylbi.mm"
include "cosq14ge0.mm"
include "sqrtge0d.mm"
include "cexp.mm"
include "recnd.mm"
include "cmul.mm"
include "ax-1cn.mm"
include "coscl.mm"
include "addcl.mm"
include "halfcld.mm"
include "sqsqrtd.mm"
include "divcan2.mm"
include "fveq2d.mm"
include "halfcl.mm"
include "cos2t.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "coscld.mm"
include "sqcld.mm"
include "mulcl.mm"
include "mpan.mm"
include "pncan3.mm"
include "divcan3.mm"
include "eqtrd.mm"
include "3eqtrrd.mm"
include "sq11d.mm"

theorem cos2h
  let cA: class A


  assert |- ( A e. ( -u _pi [,] _pi ) -> ( cos ` ( A / 2 ) ) = ( sqrt ` ( ( 1 + ( cos ` A ) ) / 2 ) ) )

  proof
    cA
    cpi
    cneg
    #
    cpi
    cicc
    co
    #
    wcel
    #
    cA
    c2
    cdiv
    co
    #
    ccos
    cfv
    #
    c1
    cA
    ccos
    cfv
    #
    caddc
    co
    #
    c2
    cdiv
    co
    #
    csqrt
    cfv
    #
    @2
    @3
    @2
    cA
    @1
    cr
    cA
    @0
    cr
    wcel
    #
    cpi
    cr
    wcel
    #
    @1
    cr
    wss
    cpi
    pire
    renegcli
    #
    pire
    @0
    cpi
    iccssre
    mp2an
    sseli
    #
    rehalfcld
    recoscld
    @2
    @7
    @2
    @6
    @2
    c1
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    1re
    @2
    cA
    @12
    recoscld
    c1
    @5
    readdcl
    #
    sylancr
    rehalfcld
    #
    @2
    cA
    cr
    wcel
    #
    cc0
    @7
    cle
    wbr
    #
    @12
    @18
    c1
    cneg
    #
    @5
    cle
    wbr
    #
    @19
    @18
    @21
    @5
    c1
    cle
    wbr
    cA
    cosbnd
    simpld
    @18
    @14
    @13
    @21
    @19
    wb
    cA
    recoscl
    1re
    @14
    @13
    wa
    #
    cc0
    @5
    @20
    cmin
    co
    #
    cle
    wbr
    #
    cc0
    @6
    cle
    wbr
    #
    @21
    @19
    @22
    @23
    @6
    cc0
    cle
    @14
    @5
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @23
    @6
    wceq
    @13
    @5
    recn
    c1
    recn
    @26
    @27
    wa
    @23
    @5
    c1
    caddc
    co
    #
    @6
    @5
    c1
    subneg
    @27
    @26
    @6
    @28
    wceq
    c1
    @5
    addcom
    ancoms
    eqtr4d
    syl2an
    breq2d
    @13
    @14
    @20
    cr
    wcel
    @24
    @21
    wb
    c1
    renegcl
    @5
    @20
    subge0
    sylan2
    @22
    @15
    @25
    @19
    wb
    @13
    @14
    @15
    @16
    ancoms
    @6
    halfnneg2
    syl
    3bitr3d
    sylancl
    mpbid
    syl
    #
    resqrtcld
    @2
    @3
    cpi
    c2
    cdiv
    co
    #
    cneg
    #
    @30
    cicc
    co
    wcel
    #
    cc0
    @4
    cle
    wbr
    @2
    @18
    @0
    cA
    cle
    wbr
    #
    cA
    cpi
    cle
    wbr
    #
    w3a
    @32
    @0
    cpi
    cA
    @11
    pire
    elicc2i
    @18
    @33
    @34
    @32
    @18
    @33
    @34
    wa
    #
    @32
    @18
    @35
    @31
    @3
    cle
    wbr
    #
    @3
    @30
    cle
    wbr
    #
    wa
    #
    @32
    @18
    @33
    @36
    @34
    @37
    @18
    @33
    @0
    c2
    cdiv
    co
    #
    @3
    cle
    wbr
    #
    @36
    @9
    @18
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    @33
    @40
    wb
    @11
    @41
    @42
    2re
    2pos
    pm3.2i
    #
    @0
    cA
    c2
    lediv1
    mp3an13
    @31
    @39
    @3
    cle
    cpi
    cc
    wcel
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    #
    @31
    @39
    wceq
    picn
    2cn
    2ne0
    cpi
    c2
    divneg
    mp3an
    breq1i
    syl6bbr
    @18
    @10
    @43
    @34
    @37
    wb
    pire
    @44
    cA
    cpi
    c2
    lediv1
    mp3an23
    anbi12d
    @18
    @3
    cxr
    wcel
    #
    @32
    @38
    wb
    #
    @18
    @3
    cA
    rehalfcl
    rexrd
    @31
    cxr
    wcel
    @30
    cxr
    wcel
    @47
    @48
    @31
    @30
    halfpire
    renegcli
    rexri
    @30
    halfpire
    rexri
    @31
    @30
    @3
    elicc4
    mp3an12
    syl
    bitr4d
    biimpd
    3impib
    sylbi
    @3
    cosq14ge0
    syl
    @2
    @7
    @17
    @29
    sqrtge0d
    @2
    cA
    cc
    wcel
    #
    @4
    c2
    cexp
    co
    #
    @8
    c2
    cexp
    co
    #
    wceq
    @2
    cA
    @12
    recnd
    @49
    @51
    @7
    c1
    c2
    @50
    cmul
    co
    #
    c1
    cmin
    co
    #
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @50
    @49
    @7
    @49
    @6
    @49
    @27
    @26
    @6
    cc
    wcel
    ax-1cn
    cA
    coscl
    c1
    @5
    addcl
    sylancr
    halfcld
    sqsqrtd
    @49
    @6
    @54
    c2
    cdiv
    @49
    @5
    @53
    c1
    caddc
    @49
    c2
    @3
    cmul
    co
    #
    ccos
    cfv
    #
    @5
    @53
    @49
    @56
    cA
    ccos
    @49
    @45
    @46
    @56
    cA
    wceq
    2cn
    2ne0
    cA
    c2
    divcan2
    mp3an23
    fveq2d
    @49
    @3
    cc
    wcel
    @57
    @53
    wceq
    cA
    halfcl
    #
    @3
    cos2t
    syl
    eqtr3d
    oveq2d
    oveq1d
    @49
    @50
    cc
    wcel
    #
    @55
    @50
    wceq
    @49
    @4
    @49
    @3
    @58
    coscld
    sqcld
    @59
    @55
    @52
    c2
    cdiv
    co
    #
    @50
    @59
    @54
    @52
    c2
    cdiv
    @59
    @27
    @52
    cc
    wcel
    #
    @54
    @52
    wceq
    ax-1cn
    @45
    @59
    @61
    2cn
    c2
    @50
    mulcl
    mpan
    c1
    @52
    pncan3
    sylancr
    oveq1d
    @59
    @45
    @46
    @60
    @50
    wceq
    2cn
    2ne0
    @50
    c2
    divcan3
    mp3an23
    eqtrd
    syl
    3eqtrrd
    syl
    sq11d
end
