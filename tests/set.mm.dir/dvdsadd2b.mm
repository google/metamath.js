include "cz.mm"
include "wcel.mm"
include "cdvds.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "simpl1.mm"
include "simpl3l.mm"
include "simpl2.mm"
include "simpl3r.mm"
include "simpr.mm"
include "dvds2add.mm"
include "imp.mm"
include "syl32anc.mm"
include "cneg.mm"
include "simp3l.mm"
include "simp2.mm"
include "zaddcl.mm"
include "syl2anc.mm"
include "adantr.mm"
include "znegcld.mm"
include "wb.mm"
include "dvdsnegb.mm"
include "mpbid.mm"
include "wceq.mm"
include "cmin.mm"
include "ancoms.mm"
include "zcnd.mm"
include "cc.mm"
include "zcn.mm"
include "adantl.mm"
include "negsubd.mm"
include "pncan2d.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "impbida.mm"

theorem dvdsadd2b
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ZZ /\ B e. ZZ /\ ( C e. ZZ /\ A || C ) ) -> ( A || B <-> A || ( C + B ) ) )

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
    cA
    cC
    cdvds
    wbr
    #
    wa
    #
    w3a
    #
    cA
    cB
    cdvds
    wbr
    #
    cA
    cC
    cB
    caddc
    co
    #
    cdvds
    wbr
    #
    @5
    @6
    wa
    @0
    @2
    @1
    @3
    @6
    @8
    @0
    @1
    @4
    @6
    simpl1
    @2
    @3
    @0
    @1
    @6
    simpl3l
    @0
    @1
    @4
    @6
    simpl2
    @2
    @3
    @0
    @1
    @6
    simpl3r
    @5
    @6
    simpr
    @0
    @2
    @1
    w3a
    @3
    @6
    wa
    @8
    cA
    cC
    cB
    dvds2add
    imp
    syl32anc
    @5
    @8
    wa
    #
    cA
    @7
    cC
    cneg
    #
    caddc
    co
    #
    cB
    cdvds
    @9
    @0
    @7
    cz
    wcel
    #
    @10
    cz
    wcel
    #
    @8
    cA
    @10
    cdvds
    wbr
    #
    cA
    @11
    cdvds
    wbr
    #
    @0
    @1
    @4
    @8
    simpl1
    #
    @5
    @12
    @8
    @5
    @2
    @1
    @12
    @0
    @1
    @2
    @3
    simp3l
    #
    @0
    @1
    @4
    simp2
    cC
    cB
    zaddcl
    #
    syl2anc
    adantr
    @5
    @13
    @8
    @5
    cC
    @17
    znegcld
    adantr
    @5
    @8
    simpr
    @9
    @3
    @14
    @2
    @3
    @0
    @1
    @8
    simpl3r
    @9
    @0
    @2
    @3
    @14
    wb
    @16
    @2
    @3
    @0
    @1
    @8
    simpl3l
    #
    cA
    cC
    dvdsnegb
    syl2anc
    mpbid
    @0
    @12
    @13
    w3a
    @8
    @14
    wa
    @15
    cA
    @7
    @10
    dvds2add
    imp
    syl32anc
    @9
    @1
    @2
    @11
    cB
    wceq
    @0
    @1
    @4
    @8
    simpl2
    @19
    @1
    @2
    wa
    #
    @11
    @7
    cC
    cmin
    co
    cB
    @20
    @7
    cC
    @20
    @7
    @2
    @1
    @12
    @18
    ancoms
    zcnd
    @2
    cC
    cc
    wcel
    @1
    cC
    zcn
    adantl
    #
    negsubd
    @20
    cC
    cB
    @21
    @1
    cB
    cc
    wcel
    @2
    cB
    zcn
    adantr
    pncan2d
    eqtrd
    syl2anc
    breqtrd
    impbida
end
