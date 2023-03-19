include "com.mm"
include "wcel.mm"
include "coa.mm"
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
include "nnacl.mm"
include "nna0.mm"
include "syl.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "suceq.mm"
include "nnasuc.mm"
include "sylan.mm"
include "sylan2.mm"
include "eqtrd.mm"
include "anassrs.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "finds2.mm"
include "vtoclga.mm"
include "com12.mm"
include "3impia.mm"

theorem nnaass
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. _om /\ B e. _om /\ C e. _om ) -> ( ( A +o B ) +o C ) = ( A +o ( B +o C ) ) )

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
    coa
    co
    #
    cC
    coa
    co
    #
    cA
    cB
    cC
    coa
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
    wa
    #
    @7
    @8
    @3
    vx
    cv
    #
    coa
    co
    #
    cA
    cB
    @9
    coa
    co
    #
    coa
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
    coa
    oveq2
    @14
    @11
    @5
    cA
    coa
    @9
    cC
    cB
    coa
    oveq2
    oveq2d
    eqeq12d
    imbi2d
    @13
    @3
    c0
    coa
    co
    #
    cA
    cB
    c0
    coa
    co
    #
    coa
    co
    #
    wceq
    @3
    vy
    cv
    #
    coa
    co
    #
    cA
    cB
    @18
    coa
    co
    #
    coa
    co
    #
    wceq
    #
    @3
    @18
    csuc
    #
    coa
    co
    #
    cA
    cB
    @23
    coa
    co
    #
    coa
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
    coa
    oveq2
    @28
    @11
    @16
    cA
    coa
    @9
    c0
    cB
    coa
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
    coa
    oveq2
    @29
    @11
    @20
    cA
    coa
    @9
    @18
    cB
    coa
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
    coa
    oveq2
    @30
    @11
    @25
    cA
    coa
    @9
    @23
    cB
    coa
    oveq2
    oveq2d
    eqeq12d
    @8
    @15
    @3
    @17
    @8
    @3
    com
    wcel
    #
    @15
    @3
    wceq
    cA
    cB
    nnacl
    #
    @3
    nna0
    syl
    @1
    @17
    @3
    wceq
    @0
    @1
    @16
    cB
    cA
    coa
    cB
    nna0
    oveq2d
    adantl
    eqtr4d
    @8
    @18
    com
    wcel
    #
    @22
    @27
    wi
    @22
    @27
    @8
    @33
    wa
    #
    @19
    csuc
    #
    @21
    csuc
    #
    wceq
    @19
    @21
    suceq
    @34
    @24
    @35
    @26
    @36
    @8
    @31
    @33
    @24
    @35
    wceq
    @32
    @3
    @18
    nnasuc
    sylan
    @0
    @1
    @33
    @26
    @36
    wceq
    @0
    @1
    @33
    wa
    #
    wa
    @26
    cA
    @20
    csuc
    #
    coa
    co
    #
    @36
    @37
    @26
    @39
    wceq
    @0
    @37
    @25
    @38
    cA
    coa
    cB
    @18
    nnasuc
    oveq2d
    adantl
    @37
    @0
    @20
    com
    wcel
    @39
    @36
    wceq
    cB
    @18
    nnacl
    cA
    @20
    nnasuc
    sylan2
    eqtrd
    anassrs
    eqeq12d
    syl5ibr
    expcom
    finds2
    vtoclga
    com12
    3impia
end
