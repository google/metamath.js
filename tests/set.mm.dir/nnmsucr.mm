include "com.mm"
include "wcel.mm"
include "csuc.mm"
include "comu.mm"
include "co.mm"
include "coa.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "oveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "c0.mm"
include "peano2.mm"
include "nnm0.mm"
include "syl.mm"
include "eqtr4d.mm"
include "peano1.mm"
include "nnmcl.mm"
include "mpan2.mm"
include "nna0.mm"
include "wa.mm"
include "oveq1.mm"
include "peano2b.mm"
include "nnmsuc.mm"
include "sylanb.mm"
include "nnaass.mm"
include "syl3an3b.mm"
include "syl3an1.mm"
include "3expb.mm"
include "anidms.mm"
include "oveq1d.mm"
include "an42s.mm"
include "nnacom.mm"
include "suceq.mm"
include "nnasuc.mm"
include "ancoms.mm"
include "3eqtr4d.mm"
include "oveq2d.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "finds2.mm"
include "vtoclga.mm"
include "impcom.mm"

theorem nnmsucr
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C


  assert |- ( ( A e. _om /\ B e. _om ) -> ( suc A .o B ) = ( ( A .o B ) +o B ) )

  proof
    cB
    com
    wcel
    cA
    com
    wcel
    #
    cA
    csuc
    #
    cB
    comu
    co
    #
    cA
    cB
    comu
    co
    #
    cB
    coa
    co
    #
    wceq
    #
    @0
    @1
    vx
    cv
    #
    comu
    co
    #
    cA
    @6
    comu
    co
    #
    @6
    coa
    co
    #
    wceq
    #
    wi
    @0
    @5
    wi
    vx
    cB
    com
    @6
    cB
    wceq
    #
    @10
    @5
    @0
    @11
    @7
    @2
    @9
    @4
    @6
    cB
    @1
    comu
    oveq2
    @11
    @8
    @3
    @6
    cB
    coa
    @6
    cB
    cA
    comu
    oveq2
    @11
    id
    oveq12d
    eqeq12d
    imbi2d
    @10
    @1
    c0
    comu
    co
    #
    cA
    c0
    comu
    co
    #
    c0
    coa
    co
    #
    wceq
    @1
    vy
    cv
    #
    comu
    co
    #
    cA
    @15
    comu
    co
    #
    @15
    coa
    co
    #
    wceq
    #
    @1
    @15
    csuc
    #
    comu
    co
    #
    cA
    @20
    comu
    co
    #
    @20
    coa
    co
    #
    wceq
    #
    @0
    vx
    vy
    @6
    c0
    wceq
    #
    @7
    @12
    @9
    @14
    @6
    c0
    @1
    comu
    oveq2
    @25
    @8
    @13
    @6
    c0
    coa
    @6
    c0
    cA
    comu
    oveq2
    @25
    id
    oveq12d
    eqeq12d
    @6
    @15
    wceq
    #
    @7
    @16
    @9
    @18
    @6
    @15
    @1
    comu
    oveq2
    @26
    @8
    @17
    @6
    @15
    coa
    @6
    @15
    cA
    comu
    oveq2
    @26
    id
    oveq12d
    eqeq12d
    @6
    @20
    wceq
    #
    @7
    @21
    @9
    @23
    @6
    @20
    @1
    comu
    oveq2
    @27
    @8
    @22
    @6
    @20
    coa
    @6
    @20
    cA
    comu
    oveq2
    @27
    id
    oveq12d
    eqeq12d
    @0
    @12
    @13
    @14
    @0
    @12
    c0
    @13
    @0
    @1
    com
    wcel
    #
    @12
    c0
    wceq
    cA
    peano2
    @1
    nnm0
    syl
    cA
    nnm0
    eqtr4d
    @0
    @13
    com
    wcel
    #
    @14
    @13
    wceq
    @0
    c0
    com
    wcel
    @29
    peano1
    cA
    c0
    nnmcl
    mpan2
    @13
    nna0
    syl
    eqtr4d
    @0
    @15
    com
    wcel
    #
    @19
    @24
    wi
    @19
    @24
    @0
    @30
    wa
    #
    @16
    @1
    coa
    co
    #
    @18
    @1
    coa
    co
    #
    wceq
    @16
    @18
    @1
    coa
    oveq1
    @31
    @21
    @32
    @23
    @33
    @0
    @28
    @30
    @21
    @32
    wceq
    cA
    peano2b
    #
    @1
    @15
    nnmsuc
    sylanb
    @31
    @17
    cA
    coa
    co
    #
    @20
    coa
    co
    #
    @17
    cA
    @20
    coa
    co
    #
    coa
    co
    #
    @23
    @33
    @31
    @36
    @38
    wceq
    #
    @31
    @0
    @30
    @39
    @31
    @17
    com
    wcel
    #
    @0
    @30
    @39
    cA
    @15
    nnmcl
    #
    @30
    @40
    @0
    @20
    com
    wcel
    @39
    @15
    peano2b
    @17
    cA
    @20
    nnaass
    syl3an3b
    syl3an1
    3expb
    anidms
    @31
    @22
    @35
    @20
    coa
    cA
    @15
    nnmsuc
    oveq1d
    @31
    @33
    @17
    @15
    @1
    coa
    co
    #
    coa
    co
    #
    @38
    @31
    @33
    @43
    wceq
    #
    @0
    @30
    @30
    @0
    @44
    @31
    @30
    @0
    @44
    @31
    @40
    @30
    @0
    @44
    @41
    @0
    @40
    @30
    @28
    @44
    @34
    @17
    @15
    @1
    nnaass
    syl3an3b
    syl3an1
    3expb
    an42s
    anidms
    @31
    @37
    @42
    @17
    coa
    @31
    cA
    @15
    coa
    co
    #
    csuc
    #
    @15
    cA
    coa
    co
    #
    csuc
    #
    @37
    @42
    @31
    @45
    @47
    wceq
    @46
    @48
    wceq
    cA
    @15
    nnacom
    @45
    @47
    suceq
    syl
    cA
    @15
    nnasuc
    @30
    @0
    @42
    @48
    wceq
    @15
    cA
    nnasuc
    ancoms
    3eqtr4d
    oveq2d
    eqtr4d
    3eqtr4d
    eqeq12d
    syl5ibr
    expcom
    finds2
    vtoclga
    impcom
end
