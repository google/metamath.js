include "com.mm"
include "wcel.mm"
include "coa.mm"
include "co.mm"
include "comu.mm"
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
include "nna0.mm"
include "adantl.mm"
include "nnmcl.mm"
include "syl.mm"
include "eqtr4d.mm"
include "nnm0.mm"
include "adantr.mm"
include "w3a.mm"
include "oveq1.mm"
include "nnasuc.mm"
include "3adant1.mm"
include "nnacl.mm"
include "nnmsuc.mm"
include "sylan2.mm"
include "3impb.mm"
include "eqtrd.mm"
include "3adant2.mm"
include "nnaass.mm"
include "syl3an1.mm"
include "syl3an2.mm"
include "3exp.mm"
include "exp4b.mm"
include "pm2.43a.mm"
include "com4r.mm"
include "pm2.43i.mm"
include "3imp.mm"
include "syl5ibr.mm"
include "com3r.mm"
include "impd.mm"
include "finds2.mm"
include "vtoclga.mm"
include "expdcom.mm"

theorem nndi
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. _om /\ B e. _om /\ C e. _om ) -> ( A .o ( B +o C ) ) = ( ( A .o B ) +o ( A .o C ) ) )

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
    cC
    coa
    co
    #
    comu
    co
    #
    cA
    cB
    comu
    co
    #
    cA
    cC
    comu
    co
    #
    coa
    co
    #
    wceq
    #
    @2
    @0
    @1
    @8
    @0
    @1
    wa
    #
    cA
    cB
    vx
    cv
    #
    coa
    co
    #
    comu
    co
    #
    @5
    cA
    @10
    comu
    co
    #
    coa
    co
    #
    wceq
    #
    wi
    @9
    @8
    wi
    vx
    cC
    com
    @10
    cC
    wceq
    #
    @15
    @8
    @9
    @16
    @12
    @4
    @14
    @7
    @16
    @11
    @3
    cA
    comu
    @10
    cC
    cB
    coa
    oveq2
    oveq2d
    @16
    @13
    @6
    @5
    coa
    @10
    cC
    cA
    comu
    oveq2
    oveq2d
    eqeq12d
    imbi2d
    @15
    cA
    cB
    c0
    coa
    co
    #
    comu
    co
    #
    @5
    cA
    c0
    comu
    co
    #
    coa
    co
    #
    wceq
    cA
    cB
    vy
    cv
    #
    coa
    co
    #
    comu
    co
    #
    @5
    cA
    @21
    comu
    co
    #
    coa
    co
    #
    wceq
    #
    cA
    cB
    @21
    csuc
    #
    coa
    co
    #
    comu
    co
    #
    @5
    cA
    @27
    comu
    co
    #
    coa
    co
    #
    wceq
    #
    @9
    vx
    vy
    @10
    c0
    wceq
    #
    @12
    @18
    @14
    @20
    @33
    @11
    @17
    cA
    comu
    @10
    c0
    cB
    coa
    oveq2
    oveq2d
    @33
    @13
    @19
    @5
    coa
    @10
    c0
    cA
    comu
    oveq2
    oveq2d
    eqeq12d
    @10
    @21
    wceq
    #
    @12
    @23
    @14
    @25
    @34
    @11
    @22
    cA
    comu
    @10
    @21
    cB
    coa
    oveq2
    oveq2d
    @34
    @13
    @24
    @5
    coa
    @10
    @21
    cA
    comu
    oveq2
    oveq2d
    eqeq12d
    @10
    @27
    wceq
    #
    @12
    @29
    @14
    @31
    @35
    @11
    @28
    cA
    comu
    @10
    @27
    cB
    coa
    oveq2
    oveq2d
    @35
    @13
    @30
    @5
    coa
    @10
    @27
    cA
    comu
    oveq2
    oveq2d
    eqeq12d
    @9
    @18
    @5
    c0
    coa
    co
    #
    @20
    @9
    @18
    @5
    @36
    @9
    @17
    cB
    cA
    comu
    @1
    @17
    cB
    wceq
    @0
    cB
    nna0
    adantl
    oveq2d
    @9
    @5
    com
    wcel
    #
    @36
    @5
    wceq
    cA
    cB
    nnmcl
    #
    @5
    nna0
    syl
    eqtr4d
    @9
    @19
    c0
    @5
    coa
    @0
    @19
    c0
    wceq
    @1
    cA
    nnm0
    adantr
    oveq2d
    eqtr4d
    @21
    com
    wcel
    #
    @0
    @1
    @26
    @32
    wi
    #
    @0
    @1
    @39
    @40
    @0
    @1
    @39
    @40
    @26
    @32
    @0
    @1
    @39
    w3a
    #
    @23
    cA
    coa
    co
    #
    @25
    cA
    coa
    co
    #
    wceq
    @23
    @25
    cA
    coa
    oveq1
    @41
    @29
    @42
    @31
    @43
    @41
    @29
    cA
    @22
    csuc
    #
    comu
    co
    #
    @42
    @41
    @28
    @44
    cA
    comu
    @1
    @39
    @28
    @44
    wceq
    @0
    cB
    @21
    nnasuc
    3adant1
    oveq2d
    @0
    @1
    @39
    @45
    @42
    wceq
    #
    @1
    @39
    wa
    @0
    @22
    com
    wcel
    @46
    cB
    @21
    nnacl
    cA
    @22
    nnmsuc
    sylan2
    3impb
    eqtrd
    @41
    @31
    @5
    @24
    cA
    coa
    co
    #
    coa
    co
    #
    @43
    @41
    @30
    @47
    @5
    coa
    @0
    @39
    @30
    @47
    wceq
    @1
    cA
    @21
    nnmsuc
    3adant2
    oveq2d
    @0
    @1
    @39
    @43
    @48
    wceq
    #
    @0
    @1
    @39
    @49
    wi
    wi
    @0
    @1
    @39
    @0
    @49
    @1
    @0
    @39
    @0
    @49
    wi
    #
    wi
    @0
    @1
    @0
    @39
    @50
    @9
    @0
    @39
    wa
    #
    @0
    @49
    @51
    @9
    @24
    com
    wcel
    #
    @0
    @49
    cA
    @21
    nnmcl
    @9
    @37
    @52
    @0
    @49
    @38
    @5
    @24
    cA
    nnaass
    syl3an1
    syl3an2
    3exp
    exp4b
    pm2.43a
    com4r
    pm2.43i
    3imp
    eqtr4d
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
