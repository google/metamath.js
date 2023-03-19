include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "cle.mm"
include "cmul.mm"
include "wb.mm"
include "wne.mm"
include "simpl.mm"
include "gt0ne0.mm"
include "jca.mm"
include "redivcl.mm"
include "3expb.mm"
include "sylan2.mm"
include "3adant3.mm"
include "simp3.mm"
include "simp2.mm"
include "lemul1.mm"
include "syl3anc.mm"
include "3adant3r.mm"
include "wceq.mm"
include "cc.mm"
include "recn.mm"
include "adantr.mm"
include "ad2antrl.mm"
include "adantl.mm"
include "divcan1d.mm"
include "breq1d.mm"
include "remulcl.mm"
include "ancoms.mm"
include "adantrr.mm"
include "3adant1.mm"
include "lediv1.mm"
include "syld3an2.mm"
include "divcan3.mm"
include "syl2an.mm"
include "breq2d.mm"
include "bitrd.mm"
include "3adant2r.mm"
include "3bitrd.mm"

theorem lediv23
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ ( B e. RR /\ 0 < B ) /\ ( C e. RR /\ 0 < C ) ) -> ( ( A / B ) <_ C <-> ( A / C ) <_ B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cc0
    cB
    clt
    wbr
    #
    wa
    #
    cC
    cr
    wcel
    #
    cc0
    cC
    clt
    wbr
    #
    wa
    #
    w3a
    #
    cA
    cB
    cdiv
    co
    #
    cC
    cle
    wbr
    #
    @8
    cB
    cmul
    co
    #
    cC
    cB
    cmul
    co
    #
    cle
    wbr
    #
    cA
    @11
    cle
    wbr
    #
    cA
    cC
    cdiv
    co
    #
    cB
    cle
    wbr
    #
    @0
    @3
    @4
    @9
    @12
    wb
    #
    @5
    @0
    @3
    @4
    w3a
    @8
    cr
    wcel
    #
    @4
    @3
    @16
    @0
    @3
    @17
    @4
    @3
    @0
    @1
    cB
    cc0
    wne
    #
    wa
    @17
    @3
    @1
    @18
    @1
    @2
    simpl
    cB
    gt0ne0
    #
    jca
    @0
    @1
    @18
    @17
    cA
    cB
    redivcl
    3expb
    sylan2
    3adant3
    @0
    @3
    @4
    simp3
    @0
    @3
    @4
    simp2
    @8
    cC
    cB
    lemul1
    syl3anc
    3adant3r
    @7
    @10
    cA
    @11
    cle
    @0
    @3
    @10
    cA
    wceq
    @6
    @0
    @3
    wa
    cA
    cB
    @0
    cA
    cc
    wcel
    @3
    cA
    recn
    adantr
    @1
    cB
    cc
    wcel
    #
    @0
    @2
    cB
    recn
    #
    ad2antrl
    @3
    @18
    @0
    @19
    adantl
    divcan1d
    3adant3
    breq1d
    @0
    @1
    @6
    @13
    @15
    wb
    @2
    @0
    @1
    @6
    w3a
    #
    @13
    @14
    @11
    cC
    cdiv
    co
    #
    cle
    wbr
    #
    @15
    @0
    @11
    cr
    wcel
    #
    @1
    @6
    @13
    @24
    wb
    @1
    @6
    @25
    @0
    @1
    @4
    @25
    @5
    @4
    @1
    @25
    cC
    cB
    remulcl
    ancoms
    adantrr
    3adant1
    cA
    @11
    cC
    lediv1
    syld3an2
    @22
    @23
    cB
    @14
    cle
    @1
    @6
    @23
    cB
    wceq
    #
    @0
    @1
    @20
    cC
    cc
    wcel
    #
    cC
    cc0
    wne
    #
    wa
    @26
    @6
    @21
    @6
    @27
    @28
    @4
    @27
    @5
    cC
    recn
    adantr
    cC
    gt0ne0
    jca
    @20
    @27
    @28
    @26
    cB
    cC
    divcan3
    3expb
    syl2an
    3adant1
    breq2d
    bitrd
    3adant2r
    3bitrd
end
