include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "w3a.mm"
include "caddc.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp2l.mm"
include "zsubcld.mm"
include "zsubcl.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "dvds2add.mm"
include "imp.mm"
include "syl31anc.mm"
include "cc.mm"
include "zcn.mm"
include "adantl.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "npncand.mm"
include "breqtrd.mm"

theorem congtr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ D e. ZZ ) /\ ( A || ( B - C ) /\ A || ( C - D ) ) ) -> A || ( B - D ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    cC
    cz
    wcel
    #
    cD
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
    cC
    cD
    cmin
    co
    #
    cdvds
    wbr
    wa
    #
    w3a
    #
    cA
    @6
    @7
    caddc
    co
    #
    cB
    cD
    cmin
    co
    cdvds
    @9
    @0
    @6
    cz
    wcel
    #
    @7
    cz
    wcel
    #
    @8
    cA
    @10
    cdvds
    wbr
    #
    @0
    @1
    @5
    @8
    simp1l
    @9
    cB
    cC
    @0
    @1
    @5
    @8
    simp1r
    @2
    @3
    @4
    @8
    simp2l
    zsubcld
    @5
    @2
    @12
    @8
    cC
    cD
    zsubcl
    3ad2ant2
    @2
    @5
    @8
    simp3
    @0
    @11
    @12
    w3a
    @8
    @13
    cA
    @6
    @7
    dvds2add
    imp
    syl31anc
    @9
    cB
    cC
    cD
    @2
    @5
    cB
    cc
    wcel
    #
    @8
    @1
    @14
    @0
    cB
    zcn
    adantl
    3ad2ant1
    @5
    @2
    cC
    cc
    wcel
    #
    @8
    @3
    @15
    @4
    cC
    zcn
    adantr
    3ad2ant2
    @5
    @2
    cD
    cc
    wcel
    #
    @8
    @4
    @16
    @3
    cD
    zcn
    adantl
    3ad2ant2
    npncand
    breqtrd
end
