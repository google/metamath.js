include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "ci.mm"
include "csin.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cpi.mm"
include "cz.mm"
include "ce.mm"
include "c1.mm"
include "cmul.mm"
include "wb.mm"
include "halfcl.mm"
include "wne.mm"
include "ax-icn.mm"
include "ine0.mm"
include "divcl.mm"
include "mp3an23.mm"
include "syl.mm"
include "sineq0.mm"
include "cneg.mm"
include "cmin.mm"
include "sinval.mm"
include "divcan2.mm"
include "fveq2d.mm"
include "mulneg1.mm"
include "sylancr.mm"
include "negeqd.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "efcl.mm"
include "negcld.mm"
include "subcld.mm"
include "2cn.mm"
include "mulcli.mm"
include "2ne0.mm"
include "mulne0i.mm"
include "diveq0.mm"
include "efne0.mm"
include "divsubdird.mm"
include "efsub.mm"
include "syl2anc.mm"
include "caddc.mm"
include "subnegd.mm"
include "2halves.mm"
include "eqtr3d.mm"
include "dividd.mm"
include "diveq0ad.mm"
include "ax-1cn.mm"
include "subeq0.mm"
include "sylancl.mm"
include "3bitr3d.mm"
include "3bitrd.mm"
include "wa.mm"
include "2cnne0.mm"
include "pm3.2i.mm"
include "divdiv32.mm"
include "picn.mm"
include "pire.mm"
include "pipos.mm"
include "gt0ne0ii.mm"
include "divdiv1.mm"
include "eleq1d.mm"

theorem efeq1
  let cA: class A


  assert |- ( A e. CC -> ( ( exp ` A ) = 1 <-> ( A / ( _i x. ( 2 x. _pi ) ) ) e. ZZ ) )

  proof
    cA
    cc
    wcel
    #
    cA
    c2
    cdiv
    co
    #
    ci
    cdiv
    co
    #
    csin
    cfv
    #
    cc0
    wceq
    #
    @2
    cpi
    cdiv
    co
    #
    cz
    wcel
    #
    cA
    ce
    cfv
    #
    c1
    wceq
    #
    cA
    ci
    c2
    cpi
    cmul
    co
    #
    cmul
    co
    cdiv
    co
    #
    cz
    wcel
    @0
    @2
    cc
    wcel
    #
    @4
    @6
    wb
    @0
    @1
    cc
    wcel
    #
    @11
    cA
    halfcl
    #
    @12
    ci
    cc
    wcel
    #
    ci
    cc0
    wne
    #
    @11
    ax-icn
    ine0
    @1
    ci
    divcl
    mp3an23
    syl
    #
    @2
    sineq0
    syl
    @0
    @4
    @1
    ce
    cfv
    #
    @1
    cneg
    #
    ce
    cfv
    #
    cmin
    co
    #
    c2
    ci
    cmul
    co
    #
    cdiv
    co
    #
    cc0
    wceq
    #
    @20
    cc0
    wceq
    #
    @8
    @0
    @3
    @22
    cc0
    @0
    @3
    ci
    @2
    cmul
    co
    #
    ce
    cfv
    #
    ci
    cneg
    @2
    cmul
    co
    #
    ce
    cfv
    #
    cmin
    co
    #
    @21
    cdiv
    co
    #
    @22
    @0
    @11
    @3
    @30
    wceq
    @16
    @2
    sinval
    syl
    @0
    @29
    @20
    @21
    cdiv
    @0
    @26
    @17
    @28
    @19
    cmin
    @0
    @25
    @1
    ce
    @0
    @12
    @25
    @1
    wceq
    #
    @13
    @12
    @14
    @15
    @31
    ax-icn
    ine0
    @1
    ci
    divcan2
    mp3an23
    syl
    #
    fveq2d
    @0
    @27
    @18
    ce
    @0
    @27
    @25
    cneg
    #
    @18
    @0
    @14
    @11
    @27
    @33
    wceq
    ax-icn
    @16
    ci
    @2
    mulneg1
    sylancr
    @0
    @25
    @1
    @32
    negeqd
    eqtrd
    fveq2d
    oveq12d
    oveq1d
    eqtrd
    eqeq1d
    @0
    @20
    cc
    wcel
    #
    @23
    @24
    wb
    #
    @0
    @17
    @19
    @0
    @12
    @17
    cc
    wcel
    @13
    @1
    efcl
    syl
    #
    @0
    @18
    cc
    wcel
    #
    @19
    cc
    wcel
    @0
    @1
    @13
    negcld
    #
    @18
    efcl
    syl
    #
    subcld
    #
    @34
    @21
    cc
    wcel
    @21
    cc0
    wne
    @35
    c2
    ci
    2cn
    ax-icn
    mulcli
    c2
    ci
    2cn
    ax-icn
    2ne0
    ine0
    mulne0i
    @20
    @21
    diveq0
    mp3an23
    syl
    @0
    @20
    @19
    cdiv
    co
    #
    cc0
    wceq
    @7
    c1
    cmin
    co
    #
    cc0
    wceq
    #
    @24
    @8
    @0
    @41
    @42
    cc0
    @0
    @41
    @17
    @19
    cdiv
    co
    #
    @19
    @19
    cdiv
    co
    #
    cmin
    co
    @42
    @0
    @17
    @19
    @19
    @36
    @39
    @39
    @0
    @37
    @19
    cc0
    wne
    @38
    @18
    efne0
    syl
    #
    divsubdird
    @0
    @44
    @7
    @45
    c1
    cmin
    @0
    @1
    @18
    cmin
    co
    #
    ce
    cfv
    #
    @44
    @7
    @0
    @12
    @37
    @48
    @44
    wceq
    @13
    @38
    @1
    @18
    efsub
    syl2anc
    @0
    @47
    cA
    ce
    @0
    @47
    @1
    @1
    caddc
    co
    cA
    @0
    @1
    @1
    @13
    @13
    subnegd
    cA
    2halves
    eqtrd
    fveq2d
    eqtr3d
    @0
    @19
    @39
    @46
    dividd
    oveq12d
    eqtrd
    eqeq1d
    @0
    @20
    @19
    @40
    @39
    @46
    diveq0ad
    @0
    @7
    cc
    wcel
    c1
    cc
    wcel
    @43
    @8
    wb
    cA
    efcl
    ax-1cn
    @7
    c1
    subeq0
    sylancl
    3bitr3d
    3bitrd
    @0
    @5
    @10
    cz
    @0
    @5
    cA
    ci
    cdiv
    co
    #
    c2
    cdiv
    co
    #
    cpi
    cdiv
    co
    #
    @10
    @0
    @2
    @50
    cpi
    cdiv
    @0
    c2
    cc
    wcel
    c2
    cc0
    wne
    wa
    #
    @14
    @15
    wa
    #
    @2
    @50
    wceq
    2cnne0
    @14
    @15
    ax-icn
    ine0
    pm3.2i
    #
    cA
    c2
    ci
    divdiv32
    mp3an23
    oveq1d
    @0
    @51
    @49
    @9
    cdiv
    co
    #
    @10
    @0
    @49
    cc
    wcel
    #
    @51
    @55
    wceq
    #
    @0
    @14
    @15
    @56
    ax-icn
    ine0
    cA
    ci
    divcl
    mp3an23
    @56
    @52
    cpi
    cc
    wcel
    #
    cpi
    cc0
    wne
    #
    wa
    @57
    2cnne0
    @58
    @59
    picn
    cpi
    pire
    pipos
    gt0ne0ii
    #
    pm3.2i
    @49
    c2
    cpi
    divdiv1
    mp3an23
    syl
    @0
    @53
    @9
    cc
    wcel
    #
    @9
    cc0
    wne
    #
    wa
    @55
    @10
    wceq
    @54
    @61
    @62
    c2
    cpi
    2cn
    picn
    mulcli
    c2
    cpi
    2cn
    picn
    2ne0
    @60
    mulne0i
    pm3.2i
    cA
    ci
    @9
    divdiv1
    mp3an23
    eqtrd
    eqtrd
    eleq1d
    3bitr3d
end
