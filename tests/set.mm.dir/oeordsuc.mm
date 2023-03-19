include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "csuc.mm"
include "coe.mm"
include "co.mm"
include "wi.mm"
include "onelon.mm"
include "ex.mm"
include "adantr.mm"
include "comu.mm"
include "wss.mm"
include "w3a.mm"
include "oewordri.mm"
include "3adant1.mm"
include "oecl.mm"
include "3adant2.mm"
include "simp1.mm"
include "omwordri.mm"
include "syl3anc.mm"
include "syld.mm"
include "wceq.mm"
include "oesuc.mm"
include "sseq1d.mm"
include "sylibrd.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "on0eln0.mm"
include "syl5ibr.mm"
include "oen0.mm"
include "simpl.mm"
include "jca.mm"
include "omordi.mm"
include "sylan.mm"
include "com23.mm"
include "mpdd.mm"
include "eleq2d.mm"
include "jcad.mm"
include "3expa.mm"
include "sucelon.mm"
include "ontr2.mm"
include "syl2an.mm"
include "anandirs.mm"
include "sylan2b.mm"
include "exp31.mm"
include "com4l.mm"
include "imp.mm"

theorem oeordsuc
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( B e. On /\ C e. On ) -> ( A e. B -> ( A ^o suc C ) e. ( B ^o suc C ) ) )

  proof
    cB
    con0
    wcel
    #
    cC
    con0
    wcel
    #
    wa
    #
    cA
    cB
    wcel
    #
    cA
    con0
    wcel
    #
    cA
    cC
    csuc
    #
    coe
    co
    #
    cB
    @5
    coe
    co
    #
    wcel
    #
    @0
    @3
    @4
    wi
    @1
    @0
    @3
    @4
    cB
    cA
    onelon
    ex
    adantr
    @0
    @1
    @3
    @4
    @8
    wi
    wi
    @4
    @0
    @1
    @3
    @8
    @4
    @0
    @1
    @3
    @8
    wi
    @4
    @0
    wa
    #
    @1
    wa
    @3
    @6
    cB
    cC
    coe
    co
    #
    cA
    comu
    co
    #
    wss
    #
    @11
    @7
    wcel
    #
    wa
    #
    @8
    @4
    @0
    @1
    @3
    @14
    wi
    @4
    @0
    @1
    w3a
    #
    @3
    @12
    @13
    @15
    @3
    cA
    cC
    coe
    co
    #
    cA
    comu
    co
    #
    @11
    wss
    #
    @12
    @15
    @3
    @16
    @10
    wss
    #
    @18
    @0
    @1
    @3
    @19
    wi
    @4
    cA
    cB
    cC
    oewordri
    3adant1
    @15
    @16
    con0
    wcel
    #
    @10
    con0
    wcel
    #
    @4
    @19
    @18
    wi
    @4
    @1
    @20
    @0
    cA
    cC
    oecl
    3adant2
    @0
    @1
    @21
    @4
    cB
    cC
    oecl
    #
    3adant1
    @4
    @0
    @1
    simp1
    @16
    @10
    cA
    omwordri
    syl3anc
    syld
    @15
    @6
    @17
    @11
    @4
    @1
    @6
    @17
    wceq
    @0
    cA
    cC
    oesuc
    3adant2
    sseq1d
    sylibrd
    @15
    @3
    @11
    @10
    cB
    comu
    co
    #
    wcel
    #
    @13
    @0
    @1
    @3
    @24
    wi
    #
    @4
    @2
    @3
    c0
    @10
    wcel
    #
    @24
    @2
    @3
    c0
    cB
    wcel
    #
    @26
    @0
    @3
    @27
    wi
    @1
    @3
    @27
    @0
    cB
    c0
    wne
    cB
    cA
    ne0i
    cB
    on0eln0
    syl5ibr
    adantr
    @2
    @27
    @26
    cB
    cC
    oen0
    ex
    syld
    @2
    @26
    @3
    @24
    @2
    @26
    @25
    @2
    @0
    @21
    wa
    @26
    @25
    @2
    @0
    @21
    @0
    @1
    simpl
    @22
    jca
    cA
    cB
    @10
    omordi
    sylan
    ex
    com23
    mpdd
    3adant1
    @15
    @7
    @23
    @11
    @0
    @1
    @7
    @23
    wceq
    @4
    cB
    cC
    oesuc
    3adant1
    eleq2d
    sylibrd
    jcad
    3expa
    @1
    @9
    @5
    con0
    wcel
    #
    @14
    @8
    wi
    #
    cC
    sucelon
    @4
    @0
    @28
    @29
    @4
    @28
    wa
    @6
    con0
    wcel
    @7
    con0
    wcel
    @29
    @0
    @28
    wa
    cA
    @5
    oecl
    cB
    @5
    oecl
    @6
    @11
    @7
    ontr2
    syl2an
    anandirs
    sylan2b
    syld
    exp31
    com4l
    imp
    mpdd
end
