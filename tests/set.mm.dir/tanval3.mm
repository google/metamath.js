include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cneg.mm"
include "cmin.mm"
include "cdiv.mm"
include "ctan.mm"
include "ax-icn.mm"
include "simpl.mm"
include "mulcl.mm"
include "sylancr.mm"
include "efcl.mm"
include "syl.mm"
include "negicn.mm"
include "subcld.mm"
include "addcld.mm"
include "cexp.mm"
include "cz.mm"
include "wceq.mm"
include "2z.mm"
include "efexp.mm"
include "sylancl.mm"
include "sqvald.mm"
include "eqtrd.mm"
include "mulneg1.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "efcan.mm"
include "eqtr2d.mm"
include "oveq12d.mm"
include "adddid.mm"
include "eqtr4d.mm"
include "a1i.mm"
include "mul12d.mm"
include "2cn.mm"
include "ax-1cn.mm"
include "addcl.mm"
include "ine0.mm"
include "simpr.mm"
include "mulne0d.mm"
include "eqnetrrd.mm"
include "mulne0bbd.mm"
include "efne0.mm"
include "divcan5d.mm"
include "subdid.mm"
include "ccos.mm"
include "cosval.mm"
include "adantr.mm"
include "2cnd.mm"
include "2ne0.mm"
include "divne0d.mm"
include "eqnetrd.mm"
include "tanval2.mm"
include "syldan.mm"
include "3eqtr4rd.mm"

theorem tanval3
  let cA: class A


  assert |- ( ( A e. CC /\ ( ( exp ` ( 2 x. ( _i x. A ) ) ) + 1 ) =/= 0 ) -> ( tan ` A ) = ( ( ( exp ` ( 2 x. ( _i x. A ) ) ) - 1 ) / ( _i x. ( ( exp ` ( 2 x. ( _i x. A ) ) ) + 1 ) ) ) )

  proof
    cA
    cc
    wcel
    #
    c2
    ci
    cA
    cmul
    co
    #
    cmul
    co
    #
    ce
    cfv
    #
    c1
    caddc
    co
    #
    cc0
    wne
    #
    wa
    #
    @1
    ce
    cfv
    #
    @7
    ci
    cneg
    #
    cA
    cmul
    co
    #
    ce
    cfv
    #
    cmin
    co
    #
    cmul
    co
    #
    @7
    ci
    @7
    @10
    caddc
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    cdiv
    co
    @11
    @14
    cdiv
    co
    #
    @3
    c1
    cmin
    co
    #
    ci
    @4
    cmul
    co
    #
    cdiv
    co
    cA
    ctan
    cfv
    #
    @6
    @11
    @14
    @7
    @6
    @7
    @10
    @6
    @1
    cc
    wcel
    #
    @7
    cc
    wcel
    @6
    ci
    cc
    wcel
    #
    @0
    @20
    ax-icn
    @0
    @5
    simpl
    #
    ci
    cA
    mulcl
    sylancr
    #
    @1
    efcl
    syl
    #
    @6
    @9
    cc
    wcel
    #
    @10
    cc
    wcel
    @6
    @8
    cc
    wcel
    @0
    @25
    negicn
    @22
    @8
    cA
    mulcl
    sylancr
    @9
    efcl
    syl
    #
    subcld
    @6
    @21
    @13
    cc
    wcel
    @14
    cc
    wcel
    ax-icn
    @6
    @7
    @10
    @24
    @26
    addcld
    #
    ci
    @13
    mulcl
    sylancr
    #
    @24
    @6
    @7
    @14
    @24
    @28
    @6
    @18
    @15
    cc0
    @6
    @18
    ci
    @7
    @13
    cmul
    co
    #
    cmul
    co
    @15
    @6
    @4
    @29
    ci
    cmul
    @6
    @4
    @7
    @7
    cmul
    co
    #
    @7
    @10
    cmul
    co
    #
    caddc
    co
    @29
    @6
    @3
    @30
    c1
    @31
    caddc
    @6
    @3
    @7
    c2
    cexp
    co
    #
    @30
    @6
    @20
    c2
    cz
    wcel
    @3
    @32
    wceq
    @23
    2z
    @1
    c2
    efexp
    sylancl
    @6
    @7
    @24
    sqvald
    eqtrd
    #
    @6
    @31
    @7
    @1
    cneg
    #
    ce
    cfv
    #
    cmul
    co
    #
    c1
    @6
    @10
    @35
    @7
    cmul
    @6
    @9
    @34
    ce
    @6
    @21
    @0
    @9
    @34
    wceq
    ax-icn
    @22
    ci
    cA
    mulneg1
    sylancr
    fveq2d
    oveq2d
    @6
    @20
    @36
    c1
    wceq
    @23
    @1
    efcan
    syl
    eqtr2d
    #
    oveq12d
    @6
    @7
    @7
    @10
    @24
    @24
    @26
    adddid
    eqtr4d
    oveq2d
    @6
    ci
    @7
    @13
    @21
    @6
    ax-icn
    a1i
    #
    @24
    @27
    mul12d
    eqtrd
    #
    @6
    ci
    @4
    @38
    @6
    @3
    cc
    wcel
    #
    c1
    cc
    wcel
    @4
    cc
    wcel
    @6
    @2
    cc
    wcel
    #
    @40
    @6
    c2
    cc
    wcel
    @20
    @41
    2cn
    @23
    c2
    @1
    mulcl
    sylancr
    @2
    efcl
    syl
    ax-1cn
    @3
    c1
    addcl
    sylancl
    ci
    cc0
    wne
    @6
    ine0
    a1i
    @0
    @5
    simpr
    mulne0d
    eqnetrrd
    mulne0bbd
    #
    @6
    @20
    @7
    cc0
    wne
    @23
    @1
    efne0
    syl
    divcan5d
    @6
    @17
    @12
    @18
    @15
    cdiv
    @6
    @17
    @30
    @31
    cmin
    co
    @12
    @6
    @3
    @30
    c1
    @31
    cmin
    @33
    @37
    oveq12d
    @6
    @7
    @7
    @10
    @24
    @24
    @26
    subdid
    eqtr4d
    @39
    oveq12d
    @0
    @5
    cA
    ccos
    cfv
    #
    cc0
    wne
    @19
    @16
    wceq
    @6
    @43
    @13
    c2
    cdiv
    co
    #
    cc0
    @0
    @43
    @44
    wceq
    @5
    cA
    cosval
    adantr
    @6
    @13
    c2
    @27
    @6
    2cnd
    @6
    ci
    @13
    @38
    @27
    @42
    mulne0bbd
    c2
    cc0
    wne
    @6
    2ne0
    a1i
    divne0d
    eqnetrd
    cA
    tanval2
    syldan
    3eqtr4rd
end
