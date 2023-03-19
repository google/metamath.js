include "cc.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "csin.mm"
include "cfv.mm"
include "cdiv.mm"
include "ce.mm"
include "cneg.mm"
include "cmin.mm"
include "c2.mm"
include "c1.mm"
include "ixi.mm"
include "oveq1i.mm"
include "wceq.mm"
include "ax-icn.mm"
include "mulass.mm"
include "mp3an12.mm"
include "mulm1.mm"
include "3eqtr3a.mm"
include "fveq2d.mm"
include "mulneg1i.mm"
include "negeqi.mm"
include "negneg1e1.mm"
include "eqtri.mm"
include "negicn.mm"
include "mulid2.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "mulcl.mm"
include "mpan.mm"
include "sinval.mm"
include "syl.mm"
include "irec.mm"
include "negnegi.mm"
include "ine0.mm"
include "reccli.mm"
include "efcl.mm"
include "negcl.mm"
include "subcld.mm"
include "halfcld.mm"
include "mulneg12.mm"
include "sylancr.mm"
include "2cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "divnegd.mm"
include "negsubdi2d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "divrec2d.mm"
include "divdiv1d.mm"
include "3eqtr2d.mm"
include "syl5eqr.mm"
include "3eqtr4d.mm"
include "divcan3d.mm"

theorem sinhval
  let cA: class A


  assert |- ( A e. CC -> ( ( sin ` ( _i x. A ) ) / _i ) = ( ( ( exp ` A ) - ( exp ` -u A ) ) / 2 ) )

  proof
    cA
    cc
    wcel
    #
    ci
    cA
    cmul
    co
    #
    csin
    cfv
    #
    ci
    cdiv
    co
    ci
    cA
    ce
    cfv
    #
    cA
    cneg
    #
    ce
    cfv
    #
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cmul
    co
    #
    ci
    cdiv
    co
    @7
    @0
    @2
    @8
    ci
    cdiv
    @0
    ci
    @1
    cmul
    co
    #
    ce
    cfv
    #
    ci
    cneg
    #
    @1
    cmul
    co
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
    @5
    @3
    cmin
    co
    #
    @15
    cdiv
    co
    #
    @2
    @8
    @0
    @14
    @17
    @15
    cdiv
    @0
    @10
    @5
    @13
    @3
    cmin
    @0
    @9
    @4
    ce
    @0
    ci
    ci
    cmul
    co
    #
    cA
    cmul
    co
    #
    c1
    cneg
    #
    cA
    cmul
    co
    @9
    @4
    @19
    @21
    cA
    cmul
    ixi
    oveq1i
    ci
    cc
    wcel
    #
    @22
    @0
    @20
    @9
    wceq
    ax-icn
    ax-icn
    ci
    ci
    cA
    mulass
    mp3an12
    cA
    mulm1
    3eqtr3a
    fveq2d
    @0
    @12
    cA
    ce
    @0
    @11
    ci
    cmul
    co
    #
    cA
    cmul
    co
    #
    c1
    cA
    cmul
    co
    @12
    cA
    @23
    c1
    cA
    cmul
    @23
    @19
    cneg
    #
    c1
    ci
    ci
    ax-icn
    ax-icn
    mulneg1i
    @25
    @21
    cneg
    c1
    @19
    @21
    ixi
    negeqi
    negneg1e1
    eqtri
    eqtri
    oveq1i
    @11
    cc
    wcel
    @22
    @0
    @24
    @12
    wceq
    negicn
    ax-icn
    @11
    ci
    cA
    mulass
    mp3an12
    cA
    mulid2
    3eqtr3a
    fveq2d
    oveq12d
    oveq1d
    @0
    @1
    cc
    wcel
    #
    @2
    @16
    wceq
    @22
    @0
    @26
    ax-icn
    ci
    cA
    mulcl
    mpan
    @1
    sinval
    syl
    @0
    @8
    c1
    ci
    cdiv
    co
    #
    cneg
    #
    @7
    cmul
    co
    #
    @18
    @28
    ci
    @7
    cmul
    @28
    @11
    cneg
    ci
    @27
    @11
    irec
    negeqi
    ci
    ax-icn
    negnegi
    eqtri
    oveq1i
    @0
    @29
    @27
    @7
    cneg
    #
    cmul
    co
    #
    @18
    @0
    @27
    cc
    wcel
    @7
    cc
    wcel
    @29
    @31
    wceq
    ci
    ax-icn
    ine0
    reccli
    @0
    @6
    @0
    @3
    @5
    cA
    efcl
    #
    @0
    @4
    cc
    wcel
    @5
    cc
    wcel
    cA
    negcl
    @4
    efcl
    syl
    #
    subcld
    #
    halfcld
    #
    @27
    @7
    mulneg12
    sylancr
    @0
    @31
    @27
    @17
    c2
    cdiv
    co
    #
    cmul
    co
    @36
    ci
    cdiv
    co
    @18
    @0
    @30
    @36
    @27
    cmul
    @0
    @30
    @6
    cneg
    #
    c2
    cdiv
    co
    @36
    @0
    @6
    c2
    @34
    @0
    2cnd
    #
    c2
    cc0
    wne
    @0
    2ne0
    a1i
    #
    divnegd
    @0
    @37
    @17
    c2
    cdiv
    @0
    @3
    @5
    @32
    @33
    negsubdi2d
    oveq1d
    eqtrd
    oveq2d
    @0
    @36
    ci
    @0
    @17
    @0
    @5
    @3
    @33
    @32
    subcld
    #
    halfcld
    @22
    @0
    ax-icn
    a1i
    #
    ci
    cc0
    wne
    @0
    ine0
    a1i
    #
    divrec2d
    @0
    @17
    c2
    ci
    @40
    @38
    @41
    @39
    @42
    divdiv1d
    3eqtr2d
    eqtrd
    syl5eqr
    3eqtr4d
    oveq1d
    @0
    @7
    ci
    @35
    @41
    @42
    divcan3d
    eqtrd
end
