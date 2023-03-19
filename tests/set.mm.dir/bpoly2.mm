include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cbp.mm"
include "co.mm"
include "cexp.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "cv.mm"
include "cbc.mm"
include "caddc.mm"
include "cdiv.mm"
include "cmul.mm"
include "csu.mm"
include "c6.mm"
include "cn0.mm"
include "wceq.mm"
include "2nn0.mm"
include "bpolyval.mm"
include "mpan.mm"
include "2m1e1.mm"
include "0p1e1.mm"
include "eqtr4i.mm"
include "oveq2i.mm"
include "sumeq1i.mm"
include "c3.mm"
include "cneg.mm"
include "cuz.mm"
include "cfv.mm"
include "0nn0.mm"
include "nn0uz.mm"
include "eleqtri.mm"
include "a1i.mm"
include "wo.mm"
include "cpr.mm"
include "cz.mm"
include "0z.mm"
include "fzpr.mm"
include "ax-mp.mm"
include "eleq2i.mm"
include "vex.mm"
include "elpr.mm"
include "bitri.mm"
include "wa.mm"
include "oveq2.mm"
include "bcn0.mm"
include "syl6eq.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "2cn.mm"
include "subid1i.mm"
include "oveq1i.mm"
include "df-3.mm"
include "oveq12d.mm"
include "bpoly0.mm"
include "oveq2d.mm"
include "3cn.mm"
include "3ne0.mm"
include "reccli.mm"
include "mulid2i.mm"
include "sylan9eqr.mm"
include "syl6eqel.mm"
include "eqeq2i.mm"
include "bcn1.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "mp2an.mm"
include "sylbi.mm"
include "bpoly1.mm"
include "halfcn.mm"
include "subcl.mm"
include "mpan2.mm"
include "wne.mm"
include "2ne0.mm"
include "divcan2.mm"
include "mp3an23.mm"
include "syl.mm"
include "eqtrd.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "fsump1.mm"
include "fsum1.mm"
include "sylancr.mm"
include "addsub12.mm"
include "mp3an13.mm"
include "negsubdi2i.mm"
include "halfthird.mm"
include "negeqi.mm"
include "eqtr3i.mm"
include "6cn.mm"
include "6re.mm"
include "6pos.mm"
include "gt0ne0ii.mm"
include "negsub.mm"
include "3eqtrd.mm"
include "syl5eq.mm"
include "sqcl.mm"
include "subsub.mm"
include "mp3an3.mm"
include "mpancom.mm"

theorem bpoly2
  let cX: class X
  let vk: setvar k


  assert |- ( X e. CC -> ( 2 BernPoly X ) = ( ( ( X ^ 2 ) - X ) + ( 1 / 6 ) ) )

  proof
    cX
    cc
    wcel
    #
    c2
    cX
    cbp
    co
    #
    cX
    c2
    cexp
    co
    #
    cc0
    c2
    c1
    cmin
    co
    #
    cfz
    co
    #
    c2
    vk
    cv
    #
    cbc
    co
    #
    @5
    cX
    cbp
    co
    #
    c2
    @5
    cmin
    co
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmin
    co
    #
    @2
    cX
    c1
    c6
    cdiv
    co
    #
    cmin
    co
    #
    cmin
    co
    #
    @2
    cX
    cmin
    co
    @14
    caddc
    co
    #
    c2
    cn0
    wcel
    #
    @0
    @1
    @13
    wceq
    2nn0
    vk
    c2
    cX
    bpolyval
    mpan
    @0
    @12
    @15
    @2
    cmin
    @0
    @12
    cc0
    cc0
    c1
    caddc
    co
    #
    cfz
    co
    #
    @11
    vk
    csu
    #
    @15
    @4
    @20
    @11
    vk
    @3
    @19
    cc0
    cfz
    @3
    c1
    @19
    2m1e1
    0p1e1
    eqtr4i
    oveq2i
    sumeq1i
    @0
    @21
    c1
    c3
    cdiv
    co
    #
    cX
    c1
    c2
    cdiv
    co
    #
    cmin
    co
    #
    caddc
    co
    #
    cX
    @14
    cneg
    #
    caddc
    co
    #
    @15
    @0
    @21
    cc0
    cc0
    cfz
    co
    @11
    vk
    csu
    #
    c2
    c1
    cX
    cbp
    co
    #
    c2
    cdiv
    co
    #
    cmul
    co
    #
    caddc
    co
    @25
    @0
    @11
    @31
    vk
    cc0
    cc0
    cc0
    cc0
    cuz
    cfv
    #
    wcel
    @0
    cc0
    cn0
    @32
    0nn0
    nn0uz
    eleqtri
    a1i
    @5
    @20
    wcel
    #
    @0
    @5
    cc0
    wceq
    #
    @5
    @19
    wceq
    #
    wo
    #
    @11
    cc
    wcel
    #
    @33
    @5
    cc0
    @19
    cpr
    #
    wcel
    @36
    @20
    @38
    @5
    cc0
    cz
    wcel
    #
    @20
    @38
    wceq
    0z
    cc0
    fzpr
    ax-mp
    eleq2i
    @5
    cc0
    @19
    vk
    vex
    elpr
    bitri
    @0
    @34
    @37
    @35
    @0
    @34
    wa
    @11
    @22
    cc
    @34
    @0
    @11
    c1
    cc0
    cX
    cbp
    co
    #
    c3
    cdiv
    co
    #
    cmul
    co
    #
    @22
    @34
    @6
    c1
    @10
    @41
    cmul
    @34
    @6
    c2
    cc0
    cbc
    co
    #
    c1
    @5
    cc0
    c2
    cbc
    oveq2
    @18
    @43
    c1
    wceq
    2nn0
    c2
    bcn0
    ax-mp
    syl6eq
    @34
    @7
    @40
    @9
    c3
    cdiv
    @5
    cc0
    cX
    cbp
    oveq1
    @34
    @9
    c2
    cc0
    cmin
    co
    #
    c1
    caddc
    co
    #
    c3
    @34
    @8
    @44
    c1
    caddc
    @5
    cc0
    c2
    cmin
    oveq2
    oveq1d
    @45
    c2
    c1
    caddc
    co
    c3
    @44
    c2
    c1
    caddc
    c2
    2cn
    subid1i
    oveq1i
    df-3
    eqtr4i
    syl6eq
    oveq12d
    oveq12d
    #
    @0
    @42
    c1
    @22
    cmul
    co
    @22
    @0
    @41
    @22
    c1
    cmul
    @0
    @40
    c1
    c3
    cdiv
    cX
    bpoly0
    oveq1d
    oveq2d
    @22
    c3
    3cn
    3ne0
    reccli
    #
    mulid2i
    syl6eq
    #
    sylan9eqr
    @47
    syl6eqel
    @0
    @35
    wa
    @11
    @24
    cc
    @35
    @0
    @11
    @31
    @24
    @35
    @5
    c1
    wceq
    #
    @11
    @31
    wceq
    @19
    c1
    @5
    0p1e1
    eqeq2i
    @49
    @6
    c2
    @10
    @30
    cmul
    @49
    @6
    c2
    c1
    cbc
    co
    #
    c2
    @5
    c1
    c2
    cbc
    oveq2
    @18
    @50
    c2
    wceq
    2nn0
    c2
    bcn1
    ax-mp
    syl6eq
    @49
    @7
    @29
    @9
    c2
    cdiv
    @5
    c1
    cX
    cbp
    oveq1
    @49
    @9
    @3
    c1
    caddc
    co
    #
    c2
    @49
    @8
    @3
    c1
    caddc
    @5
    c1
    c2
    cmin
    oveq2
    oveq1d
    c2
    cc
    wcel
    #
    c1
    cc
    wcel
    @51
    c2
    wceq
    2cn
    ax-1cn
    c2
    c1
    npcan
    mp2an
    syl6eq
    oveq12d
    oveq12d
    sylbi
    #
    @0
    @31
    c2
    @24
    c2
    cdiv
    co
    #
    cmul
    co
    #
    @24
    @0
    @30
    @54
    c2
    cmul
    @0
    @29
    @24
    c2
    cdiv
    cX
    bpoly1
    oveq1d
    oveq2d
    @0
    @24
    cc
    wcel
    #
    @55
    @24
    wceq
    #
    @0
    @23
    cc
    wcel
    #
    @56
    halfcn
    cX
    @23
    subcl
    mpan2
    #
    @56
    @52
    c2
    cc0
    wne
    @57
    2cn
    2ne0
    @24
    c2
    divcan2
    mp3an23
    syl
    eqtrd
    #
    sylan9eqr
    @0
    @56
    @35
    @59
    adantr
    eqeltrd
    jaodan
    sylan2b
    @53
    fsump1
    @0
    @28
    @22
    @31
    @24
    caddc
    @0
    @28
    @42
    @22
    @0
    @39
    @42
    cc
    wcel
    @28
    @42
    wceq
    0z
    @0
    @42
    @22
    cc
    @48
    @47
    syl6eqel
    @11
    @42
    vk
    cc0
    @46
    fsum1
    sylancr
    @48
    eqtrd
    @60
    oveq12d
    eqtrd
    @0
    @25
    cX
    @22
    @23
    cmin
    co
    #
    caddc
    co
    #
    @27
    @22
    cc
    wcel
    @0
    @58
    @25
    @62
    wceq
    @47
    halfcn
    @22
    cX
    @23
    addsub12
    mp3an13
    @61
    @26
    cX
    caddc
    @23
    @22
    cmin
    co
    #
    cneg
    @61
    @26
    @23
    @22
    halfcn
    @47
    negsubdi2i
    @63
    @14
    halfthird
    negeqi
    eqtr3i
    oveq2i
    syl6eq
    @0
    @14
    cc
    wcel
    #
    @27
    @15
    wceq
    c6
    6cn
    c6
    6re
    6pos
    gt0ne0ii
    reccli
    #
    cX
    @14
    negsub
    mpan2
    3eqtrd
    syl5eq
    oveq2d
    @2
    cc
    wcel
    #
    @0
    @16
    @17
    wceq
    #
    cX
    sqcl
    @66
    @0
    @64
    @67
    @65
    @2
    cX
    @14
    subsub
    mp3an3
    mpancom
    3eqtrd
end
