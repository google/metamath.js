include "com.mm"
include "wcel.mm"
include "comu.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "c0.mm"
include "csuc.mm"
include "nnmcl.mm"
include "nnm0.mm"
include "syl.mm"
include "sylan9eqr.mm"
include "eqtr4d.mm"
include "w3a.mm"
include "coa.mm"
include "oveq1.mm"
include "nnmsuc.mm"
include "stoic3.mm"
include "3adant1.mm"
include "nndi.mm"
include "syl3an2.mm"
include "3exp.mm"
include "expd.mm"
include "com34.mm"
include "pm2.43d.mm"
include "3imp.mm"
include "eqtrd.mm"
include "syl5ibr.mm"
include "com3r.mm"
include "impd.mm"
include "finds2.mm"
include "vtoclga.mm"
include "expdcom.mm"

theorem nnmass
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. _om /\ B e. _om /\ C e. _om ) -> ( ( A .o B ) .o C ) = ( A .o ( B .o C ) ) )

  proof
    cA
    com
    wcel
    #
    cB
    com
    wcel
    #
    cC
    com
    wcel
    #
    cA
    cB
    comu
    co
    #
    cC
    comu
    co
    #
    cA
    cB
    cC
    comu
    co
    #
    comu
    co
    #
    wceq
    #
    @2
    @0
    @1
    @7
    @0
    @1
    wa
    #
    @3
    vx
    cv
    #
    comu
    co
    #
    cA
    cB
    @9
    comu
    co
    #
    comu
    co
    #
    wceq
    #
    wi
    @8
    @7
    wi
    vx
    cC
    com
    @9
    cC
    wceq
    #
    @13
    @7
    @8
    @14
    @10
    @4
    @12
    @6
    @9
    cC
    @3
    comu
    oveq2
    @14
    @11
    @5
    cA
    comu
    @9
    cC
    cB
    comu
    oveq2
    oveq2d
    eqeq12d
    imbi2d
    @13
    @3
    c0
    comu
    co
    #
    cA
    cB
    c0
    comu
    co
    #
    comu
    co
    #
    wceq
    @3
    vy
    cv
    #
    comu
    co
    #
    cA
    cB
    @18
    comu
    co
    #
    comu
    co
    #
    wceq
    #
    @3
    @18
    csuc
    #
    comu
    co
    #
    cA
    cB
    @23
    comu
    co
    #
    comu
    co
    #
    wceq
    #
    @8
    vx
    vy
    @9
    c0
    wceq
    #
    @10
    @15
    @12
    @17
    @9
    c0
    @3
    comu
    oveq2
    @28
    @11
    @16
    cA
    comu
    @9
    c0
    cB
    comu
    oveq2
    oveq2d
    eqeq12d
    @9
    @18
    wceq
    #
    @10
    @19
    @12
    @21
    @9
    @18
    @3
    comu
    oveq2
    @29
    @11
    @20
    cA
    comu
    @9
    @18
    cB
    comu
    oveq2
    oveq2d
    eqeq12d
    @9
    @23
    wceq
    #
    @10
    @24
    @12
    @26
    @9
    @23
    @3
    comu
    oveq2
    @30
    @11
    @25
    cA
    comu
    @9
    @23
    cB
    comu
    oveq2
    oveq2d
    eqeq12d
    @8
    @15
    c0
    @17
    @8
    @3
    com
    wcel
    #
    @15
    c0
    wceq
    cA
    cB
    nnmcl
    #
    @3
    nnm0
    syl
    @1
    @0
    @17
    cA
    c0
    comu
    co
    c0
    @1
    @16
    c0
    cA
    comu
    cB
    nnm0
    oveq2d
    cA
    nnm0
    sylan9eqr
    eqtr4d
    @18
    com
    wcel
    #
    @0
    @1
    @22
    @27
    wi
    #
    @0
    @1
    @33
    @34
    @0
    @1
    @33
    @34
    @22
    @27
    @0
    @1
    @33
    w3a
    #
    @19
    @3
    coa
    co
    #
    @21
    @3
    coa
    co
    #
    wceq
    @19
    @21
    @3
    coa
    oveq1
    @35
    @24
    @36
    @26
    @37
    @0
    @1
    @31
    @33
    @24
    @36
    wceq
    @32
    @3
    @18
    nnmsuc
    stoic3
    @35
    @26
    cA
    @20
    cB
    coa
    co
    #
    comu
    co
    #
    @37
    @35
    @25
    @38
    cA
    comu
    @1
    @33
    @25
    @38
    wceq
    @0
    cB
    @18
    nnmsuc
    3adant1
    oveq2d
    @0
    @1
    @33
    @39
    @37
    wceq
    #
    @0
    @1
    @33
    @40
    wi
    @0
    @1
    @33
    @1
    @40
    @0
    @1
    @33
    @1
    @40
    wi
    @0
    @1
    @33
    wa
    #
    @1
    @40
    @41
    @0
    @20
    com
    wcel
    @1
    @40
    cB
    @18
    nnmcl
    cA
    @20
    cB
    nndi
    syl3an2
    3exp
    expd
    com34
    pm2.43d
    3imp
    eqtrd
    eqeq12d
    syl5ibr
    3exp
    com3r
    impd
    finds2
    vtoclga
    expdcom
    3imp
end
