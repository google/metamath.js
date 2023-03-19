include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "caddc.mm"
include "wi.mm"
include "simpl1.mm"
include "zsubcl.mm"
include "3adant1.mm"
include "adantr.mm"
include "adantl.mm"
include "dvds2add.mm"
include "syl3anc.mm"
include "3impia.mm"
include "wceq.mm"
include "simpl2.mm"
include "zcnd.mm"
include "cc.mm"
include "zcn.mm"
include "ad2antrl.mm"
include "simpl3.mm"
include "ad2antll.mm"
include "addsub4d.mm"
include "3adant3.mm"
include "breqtrrd.mm"

theorem congadd
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E


  assert |- ( ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) /\ ( D e. ZZ /\ E e. ZZ ) /\ ( A || ( B - C ) /\ A || ( D - E ) ) ) -> A || ( ( B + D ) - ( C + E ) ) )

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
    #
    cdvds
    wbr
    cA
    cD
    cE
    cmin
    co
    #
    cdvds
    wbr
    wa
    #
    w3a
    cA
    @7
    @8
    caddc
    co
    #
    cB
    cD
    caddc
    co
    cC
    cE
    caddc
    co
    cmin
    co
    #
    cdvds
    @3
    @6
    @9
    cA
    @10
    cdvds
    wbr
    #
    @3
    @6
    wa
    #
    @0
    @7
    cz
    wcel
    #
    @8
    cz
    wcel
    #
    @9
    @12
    wi
    @0
    @1
    @2
    @6
    simpl1
    @3
    @14
    @6
    @1
    @2
    @14
    @0
    cB
    cC
    zsubcl
    3adant1
    adantr
    @6
    @15
    @3
    cD
    cE
    zsubcl
    adantl
    cA
    @7
    @8
    dvds2add
    syl3anc
    3impia
    @3
    @6
    @11
    @10
    wceq
    @9
    @13
    cB
    cD
    cC
    cE
    @13
    cB
    @0
    @1
    @2
    @6
    simpl2
    zcnd
    @4
    cD
    cc
    wcel
    @3
    @5
    cD
    zcn
    ad2antrl
    @13
    cC
    @0
    @1
    @2
    @6
    simpl3
    zcnd
    @5
    cE
    cc
    wcel
    @3
    @4
    cE
    zcn
    ad2antll
    addsub4d
    3adant3
    breqtrrd
end
