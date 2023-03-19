include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cneg.mm"
include "caddc.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp2l.mm"
include "znegcld.mm"
include "simp2r.mm"
include "simp3l.mm"
include "simp3r.mm"
include "congneg.mm"
include "syl22anc.mm"
include "congadd.mm"
include "syl322anc.mm"
include "zcnd.mm"
include "negsubd.mm"
include "oveq12d.mm"
include "breqtrd.mm"

theorem congsub
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E


  assert |- ( ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) /\ ( D e. ZZ /\ E e. ZZ ) /\ ( A || ( B - C ) /\ A || ( D - E ) ) ) -> A || ( ( B - D ) - ( C - E ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cC
    cz
    wcel
    #
    w3a
    #
    cD
    cz
    wcel
    #
    cE
    cz
    wcel
    #
    wa
    #
    cA
    cB
    cC
    cmin
    co
    cdvds
    wbr
    #
    cA
    cD
    cE
    cmin
    co
    cdvds
    wbr
    #
    wa
    #
    w3a
    #
    cA
    cB
    cD
    cneg
    #
    caddc
    co
    #
    cC
    cE
    cneg
    #
    caddc
    co
    #
    cmin
    co
    #
    cB
    cD
    cmin
    co
    #
    cC
    cE
    cmin
    co
    #
    cmin
    co
    cdvds
    @10
    @0
    @1
    @2
    @11
    cz
    wcel
    @13
    cz
    wcel
    @7
    cA
    @11
    @13
    cmin
    co
    cdvds
    wbr
    #
    cA
    @15
    cdvds
    wbr
    @0
    @1
    @2
    @6
    @9
    simp11
    #
    @0
    @1
    @2
    @6
    @9
    simp12
    #
    @0
    @1
    @2
    @6
    @9
    simp13
    #
    @10
    cD
    @3
    @4
    @5
    @9
    simp2l
    #
    znegcld
    @10
    cE
    @3
    @4
    @5
    @9
    simp2r
    #
    znegcld
    @3
    @6
    @7
    @8
    simp3l
    @10
    @0
    @4
    @5
    @8
    @18
    @19
    @22
    @23
    @3
    @6
    @7
    @8
    simp3r
    cA
    cD
    cE
    congneg
    syl22anc
    cA
    cB
    cC
    @11
    @13
    congadd
    syl322anc
    @10
    @12
    @16
    @14
    @17
    cmin
    @10
    cB
    cD
    @10
    cB
    @20
    zcnd
    @10
    cD
    @22
    zcnd
    negsubd
    @10
    cC
    cE
    @10
    cC
    @21
    zcnd
    @10
    cE
    @23
    zcnd
    negsubd
    oveq12d
    breqtrd
end
