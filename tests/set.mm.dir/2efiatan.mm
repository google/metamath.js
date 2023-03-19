include "catan.mm"
include "cdm.mm"
include "wcel.mm"
include "c2.mm"
include "ci.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "c1.mm"
include "caddc.mm"
include "clog.mm"
include "cmin.mm"
include "cdiv.mm"
include "atanval.mm"
include "oveq2d.mm"
include "cc.mm"
include "2cn.mm"
include "a1i.mm"
include "ax-icn.mm"
include "atancl.mm"
include "mulassd.mm"
include "cneg.mm"
include "halfcl.mm"
include "ax-mp.mm"
include "mulassi.mm"
include "mul12i.mm"
include "2ne0.mm"
include "divcan2i.mm"
include "oveq2i.mm"
include "ixi.mm"
include "eqtri.mm"
include "3eqtri.mm"
include "oveq1i.mm"
include "ax-1cn.mm"
include "cc0.mm"
include "wne.mm"
include "atandm2.mm"
include "simp1bi.mm"
include "mulcl.mm"
include "sylancr.mm"
include "subcl.mm"
include "simp2bi.mm"
include "logcld.mm"
include "addcl.mm"
include "simp3bi.mm"
include "subcld.mm"
include "mulm1d.mm"
include "syl5eq.mm"
include "2mulicn.mm"
include "negsubdi2d.mm"
include "3eqtr3d.mm"
include "fveq2d.mm"
include "wceq.mm"
include "efsub.mm"
include "syl2anc.mm"
include "eflog.mm"
include "oveq12d.mm"
include "negsub.mm"
include "mulid1d.mm"
include "3eqtr3a.mm"
include "pnpcan2d.mm"
include "3eqtr4d.mm"
include "adddid.mm"
include "2timesd.mm"
include "oveq1d.mm"
include "subdid.mm"
include "subneg.mm"
include "eqtrd.mm"
include "addcom.mm"
include "3eqtrd.mm"
include "ine0.mm"
include "divcan5d.mm"
include "sylancl.mm"
include "atandm.mm"
include "wb.mm"
include "negicn.mm"
include "wa.mm"
include "subeq0.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "eqnetrrd.mm"
include "divsubdird.mm"
include "dividd.mm"

theorem 2efiatan
  let cA: class A


  assert |- ( A e. dom arctan -> ( exp ` ( 2 x. ( _i x. ( arctan ` A ) ) ) ) = ( ( ( 2 x. _i ) / ( A + _i ) ) - 1 ) )

  proof
    cA
    catan
    cdm
    wcel
    #
    c2
    ci
    cA
    catan
    cfv
    #
    cmul
    co
    cmul
    co
    #
    ce
    cfv
    c1
    ci
    cA
    cmul
    co
    #
    caddc
    co
    #
    clog
    cfv
    #
    c1
    @3
    cmin
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    ce
    cfv
    #
    @5
    ce
    cfv
    #
    @7
    ce
    cfv
    #
    cdiv
    co
    #
    c2
    ci
    cmul
    co
    #
    cA
    ci
    caddc
    co
    #
    cdiv
    co
    #
    c1
    cmin
    co
    #
    @0
    @2
    @8
    ce
    @0
    @13
    @1
    cmul
    co
    @13
    ci
    c2
    cdiv
    co
    #
    @7
    @5
    cmin
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    @2
    @8
    @0
    @1
    @19
    @13
    cmul
    cA
    atanval
    oveq2d
    @0
    c2
    ci
    @1
    c2
    cc
    wcel
    @0
    2cn
    a1i
    ci
    cc
    wcel
    #
    @0
    ax-icn
    a1i
    #
    cA
    atancl
    mulassd
    @0
    @13
    @17
    cmul
    co
    #
    @18
    cmul
    co
    #
    @18
    cneg
    #
    @20
    @8
    @0
    @24
    c1
    cneg
    #
    @18
    cmul
    co
    @25
    @23
    @26
    @18
    cmul
    @23
    c2
    ci
    @17
    cmul
    co
    cmul
    co
    ci
    c2
    @17
    cmul
    co
    #
    cmul
    co
    #
    @26
    c2
    ci
    @17
    2cn
    ax-icn
    @21
    @17
    cc
    wcel
    #
    ax-icn
    ci
    halfcl
    ax-mp
    #
    mulassi
    c2
    ci
    @17
    2cn
    ax-icn
    @30
    mul12i
    @28
    ci
    ci
    cmul
    co
    #
    @26
    @27
    ci
    ci
    cmul
    ci
    c2
    ax-icn
    2cn
    2ne0
    divcan2i
    oveq2i
    ixi
    eqtri
    3eqtri
    oveq1i
    @0
    @18
    @0
    @7
    @5
    @0
    @6
    @0
    c1
    cc
    wcel
    #
    @3
    cc
    wcel
    #
    @6
    cc
    wcel
    #
    ax-1cn
    @0
    @21
    cA
    cc
    wcel
    #
    @33
    ax-icn
    @0
    @35
    @6
    cc0
    wne
    #
    @4
    cc0
    wne
    #
    cA
    atandm2
    #
    simp1bi
    #
    ci
    cA
    mulcl
    sylancr
    #
    c1
    @3
    subcl
    sylancr
    #
    @0
    @35
    @36
    @37
    @38
    simp2bi
    #
    logcld
    #
    @0
    @4
    @0
    @32
    @33
    @4
    cc
    wcel
    #
    ax-1cn
    @40
    c1
    @3
    addcl
    sylancr
    #
    @0
    @35
    @36
    @37
    @38
    simp3bi
    #
    logcld
    #
    subcld
    #
    mulm1d
    syl5eq
    @0
    @13
    @17
    @18
    @13
    cc
    wcel
    @0
    2mulicn
    a1i
    #
    @29
    @0
    @30
    a1i
    @48
    mulassd
    @0
    @7
    @5
    @43
    @47
    negsubdi2d
    3eqtr3d
    3eqtr3d
    fveq2d
    @0
    @5
    cc
    wcel
    @7
    cc
    wcel
    @9
    @12
    wceq
    @47
    @43
    @5
    @7
    efsub
    syl2anc
    @0
    @12
    @4
    @6
    cdiv
    co
    #
    @15
    @14
    @14
    cdiv
    co
    #
    cmin
    co
    #
    @16
    @0
    @10
    @4
    @11
    @6
    cdiv
    @0
    @44
    @37
    @10
    @4
    wceq
    @45
    @46
    @4
    eflog
    syl2anc
    @0
    @34
    @36
    @11
    @6
    wceq
    @41
    @42
    @6
    eflog
    syl2anc
    oveq12d
    @0
    ci
    @4
    cmul
    co
    #
    ci
    @6
    cmul
    co
    #
    cdiv
    co
    @13
    @14
    cmin
    co
    #
    @14
    cdiv
    co
    @50
    @52
    @0
    @53
    @55
    @54
    @14
    cdiv
    @0
    ci
    c1
    cmul
    co
    #
    ci
    @3
    cmul
    co
    #
    caddc
    co
    #
    ci
    ci
    caddc
    co
    #
    @14
    cmin
    co
    #
    @53
    @55
    @0
    ci
    cA
    cneg
    #
    caddc
    co
    #
    ci
    cA
    cmin
    co
    #
    @58
    @60
    @0
    @21
    @35
    @62
    @63
    wceq
    ax-icn
    @39
    ci
    cA
    negsub
    sylancr
    @0
    @56
    ci
    @57
    @61
    caddc
    @0
    ci
    @22
    mulid1d
    #
    @0
    @31
    cA
    cmul
    co
    @26
    cA
    cmul
    co
    @57
    @61
    @31
    @26
    cA
    cmul
    ixi
    oveq1i
    @0
    ci
    ci
    cA
    @22
    @22
    @39
    mulassd
    @0
    cA
    @39
    mulm1d
    3eqtr3a
    #
    oveq12d
    @0
    ci
    cA
    ci
    @22
    @39
    @22
    pnpcan2d
    3eqtr4d
    @0
    ci
    c1
    @3
    @22
    @32
    @0
    ax-1cn
    a1i
    #
    @40
    adddid
    @0
    @13
    @59
    @14
    cmin
    @0
    ci
    @22
    2timesd
    oveq1d
    3eqtr4d
    @0
    @54
    @56
    @57
    cmin
    co
    #
    ci
    cA
    caddc
    co
    #
    @14
    @0
    ci
    c1
    @3
    @22
    @66
    @40
    subdid
    @0
    @67
    ci
    @61
    cmin
    co
    #
    @68
    @0
    @56
    ci
    @57
    @61
    cmin
    @64
    @65
    oveq12d
    @0
    @21
    @35
    @69
    @68
    wceq
    ax-icn
    @39
    ci
    cA
    subneg
    sylancr
    eqtrd
    @0
    @21
    @35
    @68
    @14
    wceq
    ax-icn
    @39
    ci
    cA
    addcom
    sylancr
    3eqtrd
    oveq12d
    @0
    @4
    @6
    ci
    @45
    @41
    @22
    @42
    ci
    cc0
    wne
    @0
    ine0
    a1i
    divcan5d
    @0
    @13
    @14
    @14
    @49
    @0
    @35
    @21
    @14
    cc
    wcel
    @39
    ax-icn
    cA
    ci
    addcl
    sylancl
    #
    @70
    @0
    cA
    ci
    cneg
    #
    cmin
    co
    #
    @14
    cc0
    @0
    @35
    @21
    @72
    @14
    wceq
    @39
    ax-icn
    cA
    ci
    subneg
    sylancl
    @0
    @72
    cc0
    wne
    #
    cA
    @71
    wne
    #
    @0
    @35
    @74
    cA
    ci
    wne
    cA
    atandm
    simp2bi
    @0
    @35
    @71
    cc
    wcel
    #
    @73
    @74
    wb
    @39
    negicn
    @35
    @75
    wa
    @72
    cc0
    cA
    @71
    cA
    @71
    subeq0
    necon3bid
    sylancl
    mpbird
    eqnetrrd
    #
    divsubdird
    3eqtr3d
    @0
    @51
    c1
    @15
    cmin
    @0
    @14
    @70
    @76
    dividd
    oveq2d
    3eqtrd
    3eqtrd
end
