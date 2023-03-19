include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmin.mm"
include "cmul.mm"
include "wceq.mm"
include "caddc.mm"
include "wrex.mm"
include "w3a.mm"
include "wo.mm"
include "cvv.mm"
include "wb.mm"
include "ovex.mm"
include "preq12bg.mm"
include "mpanr12.mm"
include "anbi1d.mm"
include "andir.mm"
include "df-3an.mm"
include "orbi12i.mm"
include "bitr4i.mm"
include "syl6bb.mm"
include "rexbidv.mm"
include "2rexbidv.mm"
include "r19.43.mm"
include "2rexbii.mm"
include "rexbii.mm"
include "3bitri.mm"
include "wi.mm"
include "pythagtriplem1.mm"
include "a1i.mm"
include "3ancoma.mm"
include "sylbi.mm"
include "cc.mm"
include "nncn.mm"
include "sqcld.mm"
include "addcom.mm"
include "syl2an.mm"
include "eqeq1d.mm"
include "syl5ibr.mm"
include "jaod.mm"
include "sylbid.mm"

theorem pythagtriplem2
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n

  disjoint A n
  disjoint A m
  disjoint A k
  disjoint m n
  disjoint k n
  disjoint k m
  disjoint B n
  disjoint B m
  disjoint B k
  disjoint C n
  disjoint C m
  disjoint C k
  assert |- ( ( A e. NN /\ B e. NN ) -> ( E. n e. NN E. m e. NN E. k e. NN ( { A , B } = { ( k x. ( ( m ^ 2 ) - ( n ^ 2 ) ) ) , ( k x. ( 2 x. ( m x. n ) ) ) } /\ C = ( k x. ( ( m ^ 2 ) + ( n ^ 2 ) ) ) ) -> ( ( A ^ 2 ) + ( B ^ 2 ) ) = ( C ^ 2 ) ) )

  proof
    cA
    cn
    wcel
    #
    cB
    cn
    wcel
    #
    wa
    #
    cA
    cB
    cpr
    vk
    cv
    #
    vm
    cv
    #
    c2
    cexp
    co
    #
    vn
    cv
    #
    c2
    cexp
    co
    #
    cmin
    co
    #
    cmul
    co
    #
    @3
    c2
    @4
    @6
    cmul
    co
    cmul
    co
    #
    cmul
    co
    #
    cpr
    wceq
    #
    cC
    @3
    @5
    @7
    caddc
    co
    cmul
    co
    wceq
    #
    wa
    #
    vk
    cn
    wrex
    #
    vm
    cn
    wrex
    vn
    cn
    wrex
    #
    cA
    @9
    wceq
    #
    cB
    @11
    wceq
    #
    @13
    w3a
    #
    vk
    cn
    wrex
    #
    vm
    cn
    wrex
    #
    vn
    cn
    wrex
    #
    cA
    @11
    wceq
    #
    cB
    @9
    wceq
    #
    @13
    w3a
    #
    vk
    cn
    wrex
    #
    vm
    cn
    wrex
    #
    vn
    cn
    wrex
    #
    wo
    #
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    caddc
    co
    #
    cC
    c2
    cexp
    co
    #
    wceq
    #
    @2
    @16
    @19
    @25
    wo
    #
    vk
    cn
    wrex
    #
    vm
    cn
    wrex
    vn
    cn
    wrex
    #
    @29
    @2
    @15
    @36
    vn
    vm
    cn
    cn
    @2
    @14
    @35
    vk
    cn
    @2
    @14
    @17
    @18
    wa
    #
    @23
    @24
    wa
    #
    wo
    #
    @13
    wa
    #
    @35
    @2
    @12
    @40
    @13
    @2
    @9
    cvv
    wcel
    @11
    cvv
    wcel
    @12
    @40
    wb
    @3
    @8
    cmul
    ovex
    @3
    @10
    cmul
    ovex
    cA
    cB
    @9
    @11
    cn
    cn
    cvv
    cvv
    preq12bg
    mpanr12
    anbi1d
    @41
    @38
    @13
    wa
    #
    @39
    @13
    wa
    #
    wo
    @35
    @38
    @39
    @13
    andir
    @19
    @42
    @25
    @43
    @17
    @18
    @13
    df-3an
    @23
    @24
    @13
    df-3an
    orbi12i
    bitr4i
    syl6bb
    rexbidv
    2rexbidv
    @37
    @20
    @26
    wo
    #
    vm
    cn
    wrex
    #
    vn
    cn
    wrex
    @21
    @27
    wo
    #
    vn
    cn
    wrex
    @29
    @36
    @44
    vn
    vm
    cn
    cn
    @19
    @25
    vk
    cn
    r19.43
    2rexbii
    @45
    @46
    vn
    cn
    @20
    @26
    vm
    cn
    r19.43
    rexbii
    @21
    @27
    vn
    cn
    r19.43
    3bitri
    syl6bb
    @2
    @22
    @34
    @28
    @22
    @34
    wi
    @2
    cA
    cB
    cC
    vk
    vm
    vn
    pythagtriplem1
    a1i
    @28
    @34
    @2
    @31
    @30
    caddc
    co
    #
    @33
    wceq
    #
    @28
    @24
    @23
    @13
    w3a
    #
    vk
    cn
    wrex
    #
    vm
    cn
    wrex
    vn
    cn
    wrex
    @48
    @26
    @50
    vn
    vm
    cn
    cn
    @25
    @49
    vk
    cn
    @23
    @24
    @13
    3ancoma
    rexbii
    2rexbii
    cB
    cA
    cC
    vk
    vm
    vn
    pythagtriplem1
    sylbi
    @2
    @32
    @47
    @33
    @0
    @30
    cc
    wcel
    @31
    cc
    wcel
    @32
    @47
    wceq
    @1
    @0
    cA
    cA
    nncn
    sqcld
    @1
    cB
    cB
    nncn
    sqcld
    @30
    @31
    addcom
    syl2an
    eqeq1d
    syl5ibr
    jaod
    sylbid
end
