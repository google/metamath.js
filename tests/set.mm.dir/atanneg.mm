include "catan.mm"
include "cdm.mm"
include "wcel.mm"
include "ci.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "cmul.mm"
include "cmin.mm"
include "clog.mm"
include "cfv.mm"
include "caddc.mm"
include "cc.mm"
include "wceq.mm"
include "ax-icn.mm"
include "cc0.mm"
include "wne.mm"
include "atandm2.mm"
include "simp1bi.mm"
include "mulneg2.mm"
include "sylancr.mm"
include "oveq2d.mm"
include "ax-1cn.mm"
include "mulcl.mm"
include "subneg.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "negsub.mm"
include "oveq12d.mm"
include "subcl.mm"
include "simp2bi.mm"
include "logcld.mm"
include "addcl.mm"
include "simp3bi.mm"
include "negsubdi2d.mm"
include "eqtr4d.mm"
include "halfcl.mm"
include "ax-mp.mm"
include "subcld.mm"
include "atandmneg.mm"
include "atanval.mm"
include "syl.mm"
include "negeqd.mm"
include "3eqtr4d.mm"

theorem atanneg
  let cA: class A


  assert |- ( A e. dom arctan -> ( arctan ` -u A ) = -u ( arctan ` A ) )

  proof
    cA
    catan
    cdm
    #
    wcel
    #
    ci
    c2
    cdiv
    co
    #
    c1
    ci
    cA
    cneg
    #
    cmul
    co
    #
    cmin
    co
    #
    clog
    cfv
    #
    c1
    @4
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    cmul
    co
    #
    @2
    c1
    ci
    cA
    cmul
    co
    #
    cmin
    co
    #
    clog
    cfv
    #
    c1
    @11
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    cmul
    co
    #
    cneg
    #
    @3
    catan
    cfv
    #
    cA
    catan
    cfv
    #
    cneg
    @1
    @10
    @2
    @16
    cneg
    #
    cmul
    co
    #
    @18
    @1
    @9
    @21
    @2
    cmul
    @1
    @9
    @15
    @13
    cmin
    co
    @21
    @1
    @6
    @15
    @8
    @13
    cmin
    @1
    @5
    @14
    clog
    @1
    @5
    c1
    @11
    cneg
    #
    cmin
    co
    #
    @14
    @1
    @4
    @23
    c1
    cmin
    @1
    ci
    cc
    wcel
    #
    cA
    cc
    wcel
    #
    @4
    @23
    wceq
    ax-icn
    @1
    @26
    @12
    cc0
    wne
    #
    @14
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
    mulneg2
    sylancr
    #
    oveq2d
    @1
    c1
    cc
    wcel
    #
    @11
    cc
    wcel
    #
    @24
    @14
    wceq
    ax-1cn
    @1
    @25
    @26
    @33
    ax-icn
    @30
    ci
    cA
    mulcl
    sylancr
    #
    c1
    @11
    subneg
    sylancr
    eqtrd
    fveq2d
    @1
    @7
    @12
    clog
    @1
    @7
    c1
    @23
    caddc
    co
    #
    @12
    @1
    @4
    @23
    c1
    caddc
    @31
    oveq2d
    @1
    @32
    @33
    @35
    @12
    wceq
    ax-1cn
    @34
    c1
    @11
    negsub
    sylancr
    eqtrd
    fveq2d
    oveq12d
    @1
    @13
    @15
    @1
    @12
    @1
    @32
    @33
    @12
    cc
    wcel
    ax-1cn
    @34
    c1
    @11
    subcl
    sylancr
    @1
    @26
    @27
    @28
    @29
    simp2bi
    logcld
    #
    @1
    @14
    @1
    @32
    @33
    @14
    cc
    wcel
    ax-1cn
    @34
    c1
    @11
    addcl
    sylancr
    @1
    @26
    @27
    @28
    @29
    simp3bi
    logcld
    #
    negsubdi2d
    eqtr4d
    oveq2d
    @1
    @2
    cc
    wcel
    #
    @16
    cc
    wcel
    @22
    @18
    wceq
    @25
    @38
    ax-icn
    ci
    halfcl
    ax-mp
    @1
    @13
    @15
    @36
    @37
    subcld
    @2
    @16
    mulneg2
    sylancr
    eqtrd
    @1
    @3
    @0
    wcel
    @19
    @10
    wceq
    cA
    atandmneg
    @3
    atanval
    syl
    @1
    @20
    @17
    cA
    atanval
    negeqd
    3eqtr4d
end
