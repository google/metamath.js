include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "caddc.mm"
include "eqcom.mm"
include "wb.mm"
include "subcl.mm"
include "ancoms.mm"
include "subadd.mm"
include "3expa.mm"
include "sylan.mm"
include "an4s.mm"
include "syl5bb.mm"
include "addcom.mm"
include "adantl.mm"
include "oveq1d.mm"
include "addsubass.mm"
include "3com12.mm"
include "eqtrd.mm"
include "adantlr.mm"
include "eqeq1d.mm"
include "addcl.mm"
include "3expb.mm"
include "sylan2.mm"
include "3bitr2rd.mm"

theorem addsubeq4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. CC /\ B e. CC ) /\ ( C e. CC /\ D e. CC ) ) -> ( ( A + B ) = ( C + D ) <-> ( C - A ) = ( B - D ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cC
    cc
    wcel
    #
    cD
    cc
    wcel
    #
    wa
    #
    wa
    #
    cC
    cA
    cmin
    co
    #
    cB
    cD
    cmin
    co
    #
    wceq
    #
    cD
    @7
    caddc
    co
    #
    cB
    wceq
    #
    cC
    cD
    caddc
    co
    #
    cA
    cmin
    co
    #
    cB
    wceq
    #
    cA
    cB
    caddc
    co
    @12
    wceq
    #
    @9
    @8
    @7
    wceq
    #
    @6
    @11
    @7
    @8
    eqcom
    @0
    @3
    @1
    @4
    @16
    @11
    wb
    #
    @0
    @3
    wa
    @7
    cc
    wcel
    #
    @1
    @4
    wa
    #
    @17
    @3
    @0
    @18
    cC
    cA
    subcl
    ancoms
    @19
    @18
    @17
    @1
    @4
    @18
    @17
    cB
    cD
    @7
    subadd
    3expa
    ancoms
    sylan
    an4s
    syl5bb
    @6
    @13
    @10
    cB
    @0
    @5
    @13
    @10
    wceq
    @1
    @0
    @5
    wa
    #
    @13
    cD
    cC
    caddc
    co
    #
    cA
    cmin
    co
    #
    @10
    @20
    @12
    @21
    cA
    cmin
    @5
    @12
    @21
    wceq
    @0
    cC
    cD
    addcom
    adantl
    oveq1d
    @5
    @0
    @22
    @10
    wceq
    #
    @3
    @4
    @0
    @23
    @4
    @3
    @0
    @23
    cD
    cC
    cA
    addsubass
    3com12
    3expa
    ancoms
    eqtrd
    adantlr
    eqeq1d
    @5
    @2
    @12
    cc
    wcel
    #
    @14
    @15
    wb
    #
    cC
    cD
    addcl
    @24
    @2
    @25
    @24
    @0
    @1
    @25
    @12
    cA
    cB
    subadd
    3expb
    ancoms
    sylan2
    3bitr2rd
end
