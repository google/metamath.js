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
include "wb.mm"
include "ltrec.mm"
include "3adant3.mm"
include "cmul.mm"
include "wne.mm"
include "gt0ne0.mm"
include "rereccl.mm"
include "syldan.mm"
include "ltmul2.mm"
include "syl3an2.mm"
include "syl3an1.mm"
include "cc.mm"
include "recn.mm"
include "adantr.mm"
include "jca.mm"
include "wceq.mm"
include "divrec.mm"
include "3expb.mm"
include "3adant2.mm"
include "breq12d.mm"
include "syl3an.mm"
include "3coml.mm"
include "bitr4d.mm"
include "3com12.mm"
include "bitrd.mm"

theorem ltdiv2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. RR /\ 0 < A ) /\ ( B e. RR /\ 0 < B ) /\ ( C e. RR /\ 0 < C ) ) -> ( A < B <-> ( C / B ) < ( C / A ) ) )

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
    cA
    cB
    clt
    wbr
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
    clt
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
    clt
    wbr
    #
    @2
    @5
    @9
    @12
    wb
    @8
    cA
    cB
    ltrec
    3adant3
    @5
    @2
    @8
    @12
    @15
    wb
    @5
    @2
    @8
    w3a
    @12
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
    clt
    wbr
    #
    @15
    @5
    @10
    cr
    wcel
    #
    @2
    @8
    @12
    @18
    wb
    #
    @3
    @4
    cB
    cc0
    wne
    #
    @19
    cB
    gt0ne0
    #
    cB
    rereccl
    syldan
    @2
    @19
    @11
    cr
    wcel
    #
    @8
    @20
    @0
    @1
    cA
    cc0
    wne
    #
    @23
    cA
    gt0ne0
    #
    cA
    rereccl
    syldan
    @10
    @11
    cC
    ltmul2
    syl3an2
    syl3an1
    @8
    @5
    @2
    @15
    @18
    wb
    #
    @8
    cC
    cc
    wcel
    #
    @5
    cB
    cc
    wcel
    #
    @21
    wa
    #
    @2
    cA
    cc
    wcel
    #
    @24
    wa
    #
    @26
    @6
    @27
    @7
    cC
    recn
    adantr
    @5
    @28
    @21
    @3
    @28
    @4
    cB
    recn
    adantr
    @22
    jca
    @2
    @30
    @24
    @0
    @30
    @1
    cA
    recn
    adantr
    @25
    jca
    @27
    @29
    @31
    w3a
    @13
    @16
    @14
    @17
    clt
    @27
    @29
    @13
    @16
    wceq
    #
    @31
    @27
    @28
    @21
    @32
    cC
    cB
    divrec
    3expb
    3adant3
    @27
    @31
    @14
    @17
    wceq
    #
    @29
    @27
    @30
    @24
    @33
    cC
    cA
    divrec
    3expb
    3adant2
    breq12d
    syl3an
    3coml
    bitr4d
    3com12
    bitrd
end
