include "cc.mm"
include "wcel.mm"
include "casin.mm"
include "cfv.mm"
include "csin.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cneg.mm"
include "cmin.mm"
include "c2.mm"
include "cdiv.mm"
include "wceq.mm"
include "asincl.mm"
include "sinval.mm"
include "syl.mm"
include "c1.mm"
include "cexp.mm"
include "csqrt.mm"
include "caddc.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "mpan.mm"
include "negcld.mm"
include "ax-1cn.mm"
include "sqcl.mm"
include "subcl.mm"
include "sylancr.mm"
include "sqrtcld.mm"
include "pnpcan2d.mm"
include "efiasin.mm"
include "mulneg12.mm"
include "asinneg.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "negcl.mm"
include "mulneg2.mm"
include "sqneg.mm"
include "oveq12d.mm"
include "3eqtrd.mm"
include "2timesd.mm"
include "2cn.mm"
include "mulass.mm"
include "mp3an12.mm"
include "subnegd.mm"
include "3eqtr4d.mm"
include "efcl.mm"
include "negicn.mm"
include "subcld.mm"
include "id.mm"
include "2mulicn.mm"
include "a1i.mm"
include "cc0.mm"
include "wne.mm"
include "2muline0.mm"
include "divmul2d.mm"
include "mpbird.mm"
include "eqtrd.mm"

theorem sinasin
  let cA: class A


  assert |- ( A e. CC -> ( sin ` ( arcsin ` A ) ) = A )

  proof
    cA
    cc
    wcel
    #
    cA
    casin
    cfv
    #
    csin
    cfv
    #
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
    cA
    @0
    @1
    cc
    wcel
    #
    @2
    @10
    wceq
    cA
    asincl
    #
    @1
    sinval
    syl
    @0
    @10
    cA
    wceq
    @8
    @9
    cA
    cmul
    co
    #
    wceq
    @0
    ci
    cA
    cmul
    co
    #
    c1
    cA
    c2
    cexp
    co
    #
    cmin
    co
    #
    csqrt
    cfv
    #
    caddc
    co
    #
    @14
    cneg
    #
    @17
    caddc
    co
    #
    cmin
    co
    @14
    @19
    cmin
    co
    #
    @8
    @13
    @0
    @14
    @19
    @17
    ci
    cc
    wcel
    #
    @0
    @14
    cc
    wcel
    ax-icn
    ci
    cA
    mulcl
    mpan
    #
    @0
    @14
    @23
    negcld
    @0
    @16
    @0
    c1
    cc
    wcel
    @15
    cc
    wcel
    @16
    cc
    wcel
    ax-1cn
    cA
    sqcl
    c1
    @15
    subcl
    sylancr
    sqrtcld
    pnpcan2d
    @0
    @4
    @18
    @7
    @20
    cmin
    cA
    efiasin
    @0
    @7
    ci
    cA
    cneg
    #
    casin
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    ci
    @24
    cmul
    co
    #
    c1
    @24
    c2
    cexp
    co
    #
    cmin
    co
    #
    csqrt
    cfv
    #
    caddc
    co
    #
    @20
    @0
    @6
    @26
    ce
    @0
    @6
    ci
    @1
    cneg
    #
    cmul
    co
    #
    @26
    @0
    @22
    @11
    @6
    @34
    wceq
    ax-icn
    @12
    ci
    @1
    mulneg12
    sylancr
    @0
    @25
    @33
    ci
    cmul
    cA
    asinneg
    oveq2d
    eqtr4d
    fveq2d
    @0
    @24
    cc
    wcel
    @27
    @32
    wceq
    cA
    negcl
    @24
    efiasin
    syl
    @0
    @28
    @19
    @31
    @17
    caddc
    @22
    @0
    @28
    @19
    wceq
    ax-icn
    ci
    cA
    mulneg2
    mpan
    @0
    @30
    @16
    csqrt
    @0
    @29
    @15
    c1
    cmin
    cA
    sqneg
    oveq2d
    fveq2d
    oveq12d
    3eqtrd
    oveq12d
    @0
    c2
    @14
    cmul
    co
    #
    @14
    @14
    caddc
    co
    @13
    @21
    @0
    @14
    @23
    2timesd
    c2
    cc
    wcel
    @22
    @0
    @13
    @35
    wceq
    2cn
    ax-icn
    c2
    ci
    cA
    mulass
    mp3an12
    @0
    @14
    @14
    @23
    @23
    subnegd
    3eqtr4d
    3eqtr4d
    @0
    @8
    cA
    @9
    @0
    @4
    @7
    @0
    @3
    cc
    wcel
    #
    @4
    cc
    wcel
    @0
    @22
    @11
    @36
    ax-icn
    @12
    ci
    @1
    mulcl
    sylancr
    @3
    efcl
    syl
    @0
    @6
    cc
    wcel
    #
    @7
    cc
    wcel
    @0
    @5
    cc
    wcel
    @11
    @37
    negicn
    @12
    @5
    @1
    mulcl
    sylancr
    @6
    efcl
    syl
    subcld
    @0
    id
    @9
    cc
    wcel
    @0
    2mulicn
    a1i
    @9
    cc0
    wne
    @0
    2muline0
    a1i
    divmul2d
    mpbird
    eqtrd
end
