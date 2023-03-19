include "catan.mm"
include "cdm.mm"
include "wcel.mm"
include "ci.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "caddc.mm"
include "clog.mm"
include "cmin.mm"
include "csqrt.mm"
include "atanval.mm"
include "oveq2d.mm"
include "cc.mm"
include "ax-icn.mm"
include "a1i.mm"
include "halfcl.mm"
include "mp1i.mm"
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
include "mulassd.mm"
include "cneg.mm"
include "wceq.mm"
include "2cn.mm"
include "2ne0.mm"
include "divneg.mm"
include "mp3an.mm"
include "ixi.mm"
include "oveq1i.mm"
include "divassi.mm"
include "3eqtr2i.mm"
include "halfcn.mm"
include "mulneg12.mm"
include "negsubdi2d.mm"
include "subdid.mm"
include "3eqtrd.mm"
include "syl5eqr.mm"
include "3eqtr2d.mm"
include "fveq2d.mm"
include "efsub.mm"
include "syl2anc.mm"
include "ccxp.mm"
include "cxpefd.mm"
include "cxpsqrt.mm"
include "syl.mm"
include "eqtr3d.mm"
include "oveq12d.mm"

theorem efiatan
  let cA: class A


  assert |- ( A e. dom arctan -> ( exp ` ( _i x. ( arctan ` A ) ) ) = ( ( sqrt ` ( 1 + ( _i x. A ) ) ) / ( sqrt ` ( 1 - ( _i x. A ) ) ) ) )

  proof
    cA
    catan
    cdm
    wcel
    #
    ci
    cA
    catan
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    c1
    c2
    cdiv
    co
    #
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
    cmul
    co
    #
    @3
    c1
    @4
    cmin
    co
    #
    clog
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    ce
    cfv
    #
    @7
    ce
    cfv
    #
    @10
    ce
    cfv
    #
    cdiv
    co
    #
    @5
    csqrt
    cfv
    #
    @8
    csqrt
    cfv
    #
    cdiv
    co
    @0
    @2
    @11
    ce
    @0
    @2
    ci
    ci
    c2
    cdiv
    co
    #
    @9
    @6
    cmin
    co
    #
    cmul
    co
    #
    cmul
    co
    ci
    @18
    cmul
    co
    #
    @19
    cmul
    co
    #
    @11
    @0
    @1
    @20
    ci
    cmul
    cA
    atanval
    oveq2d
    @0
    ci
    @18
    @19
    ci
    cc
    wcel
    #
    @0
    ax-icn
    a1i
    @23
    @18
    cc
    wcel
    @0
    ax-icn
    ci
    halfcl
    mp1i
    @0
    @9
    @6
    @0
    @8
    @0
    c1
    cc
    wcel
    #
    @4
    cc
    wcel
    #
    @8
    cc
    wcel
    #
    ax-1cn
    @0
    @23
    cA
    cc
    wcel
    #
    @25
    ax-icn
    @0
    @27
    @8
    cc0
    wne
    #
    @5
    cc0
    wne
    #
    cA
    atandm2
    #
    simp1bi
    ci
    cA
    mulcl
    sylancr
    #
    c1
    @4
    subcl
    sylancr
    #
    @0
    @27
    @28
    @29
    @30
    simp2bi
    #
    logcld
    #
    @0
    @5
    @0
    @24
    @25
    @5
    cc
    wcel
    #
    ax-1cn
    @31
    c1
    @4
    addcl
    sylancr
    #
    @0
    @27
    @28
    @29
    @30
    simp3bi
    #
    logcld
    #
    subcld
    #
    mulassd
    @0
    @22
    @3
    cneg
    #
    @19
    cmul
    co
    #
    @11
    @40
    @21
    @19
    cmul
    @40
    c1
    cneg
    #
    c2
    cdiv
    co
    #
    ci
    ci
    cmul
    co
    #
    c2
    cdiv
    co
    @21
    @24
    c2
    cc
    wcel
    c2
    cc0
    wne
    @40
    @43
    wceq
    ax-1cn
    2cn
    2ne0
    c1
    c2
    divneg
    mp3an
    @44
    @42
    c2
    cdiv
    ixi
    oveq1i
    ci
    ci
    c2
    ax-icn
    ax-icn
    2cn
    2ne0
    divassi
    3eqtr2i
    oveq1i
    @0
    @41
    @3
    @19
    cneg
    #
    cmul
    co
    #
    @3
    @6
    @9
    cmin
    co
    #
    cmul
    co
    @11
    @0
    @3
    cc
    wcel
    #
    @19
    cc
    wcel
    @41
    @46
    wceq
    halfcn
    @39
    @3
    @19
    mulneg12
    sylancr
    @0
    @45
    @47
    @3
    cmul
    @0
    @9
    @6
    @34
    @38
    negsubdi2d
    oveq2d
    @0
    @3
    @6
    @9
    @48
    @0
    halfcn
    a1i
    #
    @38
    @34
    subdid
    3eqtrd
    syl5eqr
    3eqtr2d
    fveq2d
    @0
    @7
    cc
    wcel
    #
    @10
    cc
    wcel
    #
    @12
    @15
    wceq
    @0
    @48
    @6
    cc
    wcel
    @50
    halfcn
    @38
    @3
    @6
    mulcl
    sylancr
    @0
    @48
    @9
    cc
    wcel
    @51
    halfcn
    @34
    @3
    @9
    mulcl
    sylancr
    @7
    @10
    efsub
    syl2anc
    @0
    @13
    @16
    @14
    @17
    cdiv
    @0
    @5
    @3
    ccxp
    co
    #
    @13
    @16
    @0
    @5
    @3
    @36
    @37
    @49
    cxpefd
    @0
    @35
    @52
    @16
    wceq
    @36
    @5
    cxpsqrt
    syl
    eqtr3d
    @0
    @8
    @3
    ccxp
    co
    #
    @14
    @17
    @0
    @8
    @3
    @32
    @33
    @49
    cxpefd
    @0
    @26
    @53
    @17
    wceq
    @32
    @8
    cxpsqrt
    syl
    eqtr3d
    oveq12d
    3eqtrd
end
