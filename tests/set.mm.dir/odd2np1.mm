include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "c1.mm"
include "caddc.mm"
include "wb.mm"
include "2z.mm"
include "divides.mm"
include "mpan.mm"
include "notbid.mm"
include "wo.mm"
include "wa.mm"
include "cr.mm"
include "cn0.mm"
include "cneg.mm"
include "elznn0.mm"
include "odd2np1lem.mm"
include "adantl.mm"
include "peano2z.mm"
include "znegcl.mm"
include "syl.mm"
include "ad2antlr.mm"
include "cc.mm"
include "zcn.mm"
include "2cn.mm"
include "mulcl.mm"
include "peano2cn.mm"
include "simpl.mm"
include "recnd.mm"
include "negcon2.mm"
include "syl2anc.mm"
include "eqcom.mm"
include "cmin.mm"
include "sylancr.mm"
include "ax-1cn.mm"
include "mulcli.mm"
include "addsubass.mm"
include "mp3an23.mm"
include "2t1e2.mm"
include "oveq1i.mm"
include "2m1e1.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "syl6req.mm"
include "adddi.mm"
include "mp3an13.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "negeqd.mm"
include "zcnd.mm"
include "mulneg2.mm"
include "negsubdi.mm"
include "sylancl.mm"
include "eqeq1d.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "biimpa.mm"
include "oveq2.mm"
include "rspcev.mm"
include "ex.mm"
include "rexlimdva.mm"
include "recn.mm"
include "syl2anr.mm"
include "mulneg1.mm"
include "syl6rbbr.mm"
include "oveq1.mm"
include "orim12d.mm"
include "syl5.mm"
include "imp.mm"
include "jaodan.mm"
include "sylbi.mm"
include "cdiv.mm"
include "halfnz.mm"
include "reeanv.mm"
include "eqtr3.mm"
include "mulcom.mm"
include "eqeq2d.mm"
include "subadd.mm"
include "mp3an3.mm"
include "subcl.mm"
include "cc0.mm"
include "wne.mm"
include "2cnne0.mm"
include "w3a.mm"
include "divmul.mm"
include "ancoms.mm"
include "subdi.mm"
include "mp3an1.mm"
include "syl2an.mm"
include "wi.mm"
include "zsubcl.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "sylbird.mm"
include "sylbid.mm"
include "rexlimivv.mm"
include "sylbir.mm"
include "mto.mm"
include "pm5.17.mm"
include "bicom.mm"
include "bitri.mm"
include "sylanblc.mm"

theorem odd2np1
  let vn: setvar n
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y

  disjoint N n
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint N k
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint N x
  disjoint N y
  assert |- ( N e. ZZ -> ( -. 2 || N <-> E. n e. ZZ ( ( 2 x. n ) + 1 ) = N ) )

  proof
    cN
    cz
    wcel
    #
    c2
    cN
    cdvds
    wbr
    #
    wn
    vk
    cv
    #
    c2
    cmul
    co
    #
    cN
    wceq
    #
    vk
    cz
    wrex
    #
    wn
    #
    c2
    vn
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    cN
    wceq
    #
    vn
    cz
    wrex
    #
    @0
    @1
    @5
    c2
    cz
    wcel
    @0
    @1
    @5
    wb
    2z
    vk
    c2
    cN
    divides
    mpan
    notbid
    @0
    @11
    @5
    wo
    #
    @11
    @5
    wa
    #
    wn
    #
    @6
    @11
    wb
    #
    @0
    cN
    cr
    wcel
    #
    cN
    cn0
    wcel
    #
    cN
    cneg
    #
    cn0
    wcel
    #
    wo
    wa
    @12
    cN
    elznn0
    @16
    @17
    @12
    @19
    @17
    @12
    @16
    vk
    vn
    cN
    odd2np1lem
    adantl
    @16
    @19
    @12
    @19
    c2
    vx
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    @18
    wceq
    #
    vx
    cz
    wrex
    #
    vy
    cv
    #
    c2
    cmul
    co
    #
    @18
    wceq
    #
    vy
    cz
    wrex
    #
    wo
    @16
    @12
    vy
    vx
    @18
    odd2np1lem
    @16
    @24
    @11
    @28
    @5
    @16
    @23
    @11
    vx
    cz
    @16
    @20
    cz
    wcel
    #
    wa
    #
    @23
    @11
    @30
    @23
    wa
    @20
    c1
    caddc
    co
    #
    cneg
    #
    cz
    wcel
    #
    c2
    @32
    cmul
    co
    #
    c1
    caddc
    co
    #
    cN
    wceq
    #
    @11
    @29
    @33
    @16
    @23
    @29
    @31
    cz
    wcel
    @33
    @20
    peano2z
    #
    @31
    znegcl
    syl
    ad2antlr
    @30
    @23
    @36
    @30
    @23
    cN
    @22
    cneg
    #
    wceq
    #
    @36
    @30
    @22
    cc
    wcel
    #
    cN
    cc
    wcel
    #
    @23
    @39
    wb
    @29
    @40
    @16
    @29
    @20
    cc
    wcel
    #
    @40
    @20
    zcn
    #
    @42
    @21
    cc
    wcel
    #
    @40
    c2
    cc
    wcel
    #
    @42
    @44
    2cn
    c2
    @20
    mulcl
    #
    mpan
    @21
    peano2cn
    syl
    syl
    adantl
    @30
    cN
    @16
    @29
    simpl
    recnd
    @22
    cN
    negcon2
    syl2anc
    @39
    @38
    cN
    wceq
    @30
    @36
    cN
    @38
    eqcom
    @30
    @38
    @35
    cN
    @29
    @38
    @35
    wceq
    @16
    @29
    @38
    c2
    @31
    cmul
    co
    #
    c1
    cmin
    co
    #
    cneg
    #
    @35
    @29
    @22
    @48
    @29
    @22
    @21
    c2
    c1
    cmul
    co
    #
    caddc
    co
    #
    c1
    cmin
    co
    #
    @48
    @29
    @52
    @21
    @50
    c1
    cmin
    co
    #
    caddc
    co
    #
    @22
    @29
    @44
    @52
    @54
    wceq
    #
    @29
    @45
    @42
    @44
    2cn
    @43
    @46
    sylancr
    @44
    @50
    cc
    wcel
    c1
    cc
    wcel
    #
    @55
    c2
    c1
    2cn
    ax-1cn
    mulcli
    ax-1cn
    @21
    @50
    c1
    addsubass
    mp3an23
    syl
    @53
    c1
    @21
    caddc
    @53
    c2
    c1
    cmin
    co
    c1
    @50
    c2
    c1
    cmin
    2t1e2
    oveq1i
    2m1e1
    eqtri
    oveq2i
    syl6req
    @29
    @47
    @51
    c1
    cmin
    @29
    @42
    @47
    @51
    wceq
    #
    @43
    @45
    @42
    @56
    @57
    2cn
    ax-1cn
    c2
    @20
    c1
    adddi
    mp3an13
    syl
    oveq1d
    eqtr4d
    negeqd
    @29
    @35
    @47
    cneg
    #
    c1
    caddc
    co
    #
    @49
    @29
    @34
    @58
    c1
    caddc
    @29
    @45
    @31
    cc
    wcel
    #
    @34
    @58
    wceq
    2cn
    @29
    @31
    @37
    zcnd
    #
    c2
    @31
    mulneg2
    sylancr
    oveq1d
    @29
    @47
    cc
    wcel
    #
    @56
    @49
    @59
    wceq
    @29
    @45
    @60
    @62
    2cn
    @61
    c2
    @31
    mulcl
    sylancr
    ax-1cn
    @47
    c1
    negsubdi
    sylancl
    eqtr4d
    eqtr4d
    adantl
    eqeq1d
    syl5bb
    bitrd
    biimpa
    @10
    @36
    vn
    @32
    cz
    @7
    @32
    wceq
    #
    @9
    @35
    cN
    @63
    @8
    @34
    c1
    caddc
    @7
    @32
    c2
    cmul
    oveq2
    oveq1d
    eqeq1d
    rspcev
    syl2anc
    ex
    rexlimdva
    @16
    @27
    @5
    vy
    cz
    @16
    @25
    cz
    wcel
    #
    wa
    #
    @27
    @5
    @65
    @27
    wa
    @25
    cneg
    #
    cz
    wcel
    #
    @66
    c2
    cmul
    co
    #
    cN
    wceq
    #
    @5
    @64
    @67
    @16
    @27
    @25
    znegcl
    ad2antlr
    @65
    @27
    @69
    @65
    @27
    cN
    @26
    cneg
    #
    wceq
    #
    @69
    @64
    @26
    cc
    wcel
    #
    @41
    @27
    @71
    wb
    @16
    @64
    @25
    cc
    wcel
    #
    @45
    @72
    @25
    zcn
    #
    2cn
    @25
    c2
    mulcl
    sylancl
    cN
    recn
    @26
    cN
    negcon2
    syl2anr
    @65
    @69
    @70
    cN
    wceq
    @71
    @65
    @68
    @70
    cN
    @64
    @68
    @70
    wceq
    #
    @16
    @64
    @73
    @45
    @75
    @74
    2cn
    @25
    c2
    mulneg1
    sylancl
    adantl
    eqeq1d
    cN
    @70
    eqcom
    syl6rbbr
    bitrd
    biimpa
    @4
    @69
    vk
    @66
    cz
    @2
    @66
    wceq
    @3
    @68
    cN
    @2
    @66
    c2
    cmul
    oveq1
    eqeq1d
    rspcev
    syl2anc
    ex
    rexlimdva
    orim12d
    syl5
    imp
    jaodan
    sylbi
    @13
    c1
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    halfnz
    @13
    @10
    @4
    wa
    #
    vk
    cz
    wrex
    vn
    cz
    wrex
    @77
    @10
    @4
    vn
    vk
    cz
    cz
    reeanv
    @78
    @77
    vn
    vk
    cz
    cz
    @78
    @9
    @3
    wceq
    #
    @7
    cz
    wcel
    #
    @2
    cz
    wcel
    #
    wa
    #
    @77
    @9
    @3
    cN
    eqtr3
    @82
    @79
    @9
    c2
    @2
    cmul
    co
    #
    wceq
    #
    @77
    @81
    @79
    @84
    wb
    @80
    @81
    @3
    @83
    @9
    @81
    @2
    cc
    wcel
    #
    @45
    @3
    @83
    wceq
    @2
    zcn
    #
    2cn
    @2
    c2
    mulcom
    sylancl
    eqeq2d
    adantl
    @82
    @84
    @83
    @8
    cmin
    co
    #
    c1
    wceq
    #
    @77
    @81
    @83
    cc
    wcel
    #
    @8
    cc
    wcel
    #
    @88
    @84
    wb
    #
    @80
    @81
    @45
    @85
    @89
    2cn
    @86
    c2
    @2
    mulcl
    sylancr
    @80
    @45
    @7
    cc
    wcel
    #
    @90
    2cn
    @7
    zcn
    #
    c2
    @7
    mulcl
    sylancr
    @89
    @90
    @56
    @91
    ax-1cn
    @83
    @8
    c1
    subadd
    mp3an3
    syl2anr
    @82
    @88
    @2
    @7
    cmin
    co
    #
    @76
    wceq
    #
    @77
    @80
    @92
    @85
    @95
    @88
    wb
    @81
    @93
    @86
    @92
    @85
    wa
    #
    @95
    c2
    @94
    cmul
    co
    #
    c1
    wceq
    #
    @88
    @85
    @92
    @95
    @98
    wb
    #
    @85
    @92
    wa
    @94
    cc
    wcel
    #
    @99
    @2
    @7
    subcl
    @56
    @100
    @45
    c2
    cc0
    wne
    wa
    #
    @99
    ax-1cn
    2cnne0
    @95
    @76
    @94
    wceq
    @56
    @100
    @101
    w3a
    @98
    @94
    @76
    eqcom
    c1
    @94
    c2
    divmul
    syl5bb
    mp3an13
    syl
    ancoms
    @96
    @97
    @87
    c1
    @85
    @92
    @97
    @87
    wceq
    #
    @45
    @85
    @92
    @102
    2cn
    c2
    @2
    @7
    subdi
    mp3an1
    ancoms
    eqeq1d
    bitrd
    syl2an
    @81
    @80
    @95
    @77
    wi
    @81
    @80
    wa
    @94
    cz
    wcel
    @95
    @77
    @2
    @7
    zsubcl
    @94
    @76
    cz
    eleq1
    syl5ibcom
    ancoms
    sylbird
    sylbird
    sylbid
    syl5
    rexlimivv
    sylbir
    mto
    @12
    @14
    wa
    @11
    @6
    wb
    @15
    @11
    @5
    pm5.17
    @11
    @6
    bicom
    bitri
    sylanblc
    bitrd
end
