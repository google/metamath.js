include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cle.mm"
include "cmul.mm"
include "wb.mm"
include "wne.mm"
include "gt0ne0.mm"
include "rereccl.mm"
include "syldan.mm"
include "3ad2ant2.mm"
include "3ad2ant1.mm"
include "simp3l.mm"
include "simp3r.mm"
include "lemul2.mm"
include "syl112anc.mm"
include "lerec.mm"
include "3adant3.mm"
include "wceq.mm"
include "cc.mm"
include "recn.mm"
include "adantr.mm"
include "jca.mm"
include "divrec.mm"
include "3expb.mm"
include "syl2an.mm"
include "3adant2.mm"
include "breq12d.mm"
include "3coml.mm"
include "3adant3r.mm"
include "3bitr4d.mm"

theorem lediv2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. RR /\ 0 < A ) /\ ( B e. RR /\ 0 < B ) /\ ( C e. RR /\ 0 < C ) ) -> ( A <_ B <-> ( C / B ) <_ ( C / A ) ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    wa
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
    c1
    cB
    cdiv
    co
    #
    c1
    cA
    cdiv
    co
    #
    cle
    wbr
    #
    cC
    @10
    cmul
    co
    #
    cC
    @11
    cmul
    co
    #
    cle
    wbr
    #
    cA
    cB
    cle
    wbr
    #
    cC
    cB
    cdiv
    co
    #
    cC
    cA
    cdiv
    co
    #
    cle
    wbr
    #
    @9
    @10
    cr
    wcel
    #
    @11
    cr
    wcel
    #
    @6
    @7
    @12
    @15
    wb
    @5
    @2
    @20
    @8
    @3
    @4
    cB
    cc0
    wne
    #
    @20
    cB
    gt0ne0
    #
    cB
    rereccl
    syldan
    3ad2ant2
    @2
    @5
    @21
    @8
    @0
    @1
    cA
    cc0
    wne
    #
    @21
    cA
    gt0ne0
    #
    cA
    rereccl
    syldan
    3ad2ant1
    @2
    @5
    @6
    @7
    simp3l
    @2
    @5
    @6
    @7
    simp3r
    @10
    @11
    cC
    lemul2
    syl112anc
    @2
    @5
    @16
    @12
    wb
    @8
    cA
    cB
    lerec
    3adant3
    @2
    @5
    @6
    @19
    @15
    wb
    #
    @7
    @6
    @2
    @5
    @26
    @6
    @2
    @5
    w3a
    @17
    @13
    @18
    @14
    cle
    @6
    @5
    @17
    @13
    wceq
    #
    @2
    @6
    cC
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @22
    wa
    @27
    @5
    cC
    recn
    #
    @5
    @29
    @22
    @3
    @29
    @4
    cB
    recn
    adantr
    @23
    jca
    @28
    @29
    @22
    @27
    cC
    cB
    divrec
    3expb
    syl2an
    3adant2
    @6
    @2
    @18
    @14
    wceq
    #
    @5
    @6
    @28
    cA
    cc
    wcel
    #
    @24
    wa
    @31
    @2
    @30
    @2
    @32
    @24
    @0
    @32
    @1
    cA
    recn
    adantr
    @25
    jca
    @28
    @32
    @24
    @31
    cC
    cA
    divrec
    3expb
    syl2an
    3adant3
    breq12d
    3coml
    3adant3r
    3bitr4d
end
