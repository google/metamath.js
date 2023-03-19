include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "codd.mm"
include "w3a.mm"
include "c2.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "cneg.mm"
include "cexp.mm"
include "cz.mm"
include "wrex.mm"
include "wb.mm"
include "oddz.mm"
include "odd2np1ALTV.mm"
include "syl.mm"
include "biimpd.mm"
include "pm2.43i.mm"
include "3ad2ant3.mm"
include "wa.mm"
include "simpl1.mm"
include "simpl2.mm"
include "2z.mm"
include "simprl.mm"
include "zmulcl.mm"
include "sylancr.mm"
include "expclzd.mm"
include "mulneg2d.mm"
include "sqneg.mm"
include "oveq1d.mm"
include "negcld.mm"
include "negne0d.mm"
include "a1i.mm"
include "simpl.mm"
include "jca.mm"
include "adantl.mm"
include "jca31.mm"
include "expmulz.mm"
include "3eqtr4d.mm"
include "expp1zd.mm"
include "simprr.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "negeqd.mm"
include "rexlimddv.mm"

theorem oexpnegnz
  let cA: class A
  let cN: class N
  let vn: setvar n
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. CC /\ A =/= 0 /\ N e. Odd ) -> ( -u A ^ N ) = -u ( A ^ N ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cN
    codd
    wcel
    #
    w3a
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
    cA
    cneg
    #
    cN
    cexp
    co
    #
    cA
    cN
    cexp
    co
    #
    cneg
    #
    wceq
    vn
    cz
    @2
    @0
    @7
    vn
    cz
    wrex
    #
    @1
    @2
    @12
    @2
    @2
    @12
    @2
    cN
    cz
    wcel
    @2
    @12
    wb
    cN
    oddz
    vn
    cN
    odd2np1ALTV
    syl
    biimpd
    pm2.43i
    3ad2ant3
    @3
    @4
    cz
    wcel
    #
    @7
    wa
    #
    wa
    #
    cA
    @5
    cexp
    co
    #
    cA
    cmul
    co
    #
    cneg
    #
    @9
    @11
    @15
    @16
    @8
    cmul
    co
    #
    @18
    @9
    @15
    @16
    cA
    @15
    cA
    @5
    @0
    @1
    @2
    @14
    simpl1
    #
    @0
    @1
    @2
    @14
    simpl2
    #
    @15
    c2
    cz
    wcel
    #
    @13
    @5
    cz
    wcel
    2z
    @3
    @13
    @7
    simprl
    c2
    @4
    zmulcl
    sylancr
    #
    expclzd
    @20
    mulneg2d
    @15
    @8
    @5
    cexp
    co
    #
    @8
    cmul
    co
    #
    @19
    @9
    @15
    @24
    @16
    @8
    cmul
    @15
    @8
    c2
    cexp
    co
    #
    @4
    cexp
    co
    #
    cA
    c2
    cexp
    co
    #
    @4
    cexp
    co
    #
    @24
    @16
    @15
    @26
    @28
    @4
    cexp
    @15
    @0
    @26
    @28
    wceq
    @20
    cA
    sqneg
    syl
    oveq1d
    @15
    @8
    cc
    wcel
    #
    @8
    cc0
    wne
    #
    wa
    @22
    @13
    wa
    #
    wa
    @24
    @27
    wceq
    @15
    @30
    @31
    @32
    @15
    cA
    @20
    negcld
    #
    @15
    cA
    @20
    @21
    negne0d
    #
    @14
    @32
    @3
    @14
    @22
    @13
    @22
    @14
    2z
    a1i
    @13
    @7
    simpl
    jca
    adantl
    #
    jca31
    @8
    c2
    @4
    expmulz
    syl
    @15
    @0
    @1
    wa
    @32
    wa
    @16
    @29
    wceq
    @15
    @0
    @1
    @32
    @20
    @21
    @35
    jca31
    cA
    c2
    @4
    expmulz
    syl
    3eqtr4d
    oveq1d
    @15
    @8
    @6
    cexp
    co
    @25
    @9
    @15
    @8
    @5
    @33
    @34
    @23
    expp1zd
    @15
    @6
    cN
    @8
    cexp
    @3
    @13
    @7
    simprr
    #
    oveq2d
    eqtr3d
    eqtr3d
    eqtr3d
    @15
    @17
    @10
    @15
    cA
    @6
    cexp
    co
    @17
    @10
    @15
    cA
    @5
    @20
    @21
    @23
    expp1zd
    @15
    @6
    cN
    cA
    cexp
    @36
    oveq2d
    eqtr3d
    negeqd
    eqtr3d
    rexlimddv
end
