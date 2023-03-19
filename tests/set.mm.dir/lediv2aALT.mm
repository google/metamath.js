include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cle.mm"
include "w3a.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wi.mm"
include "wne.mm"
include "gt0ne0.mm"
include "rereccl.mm"
include "syldan.mm"
include "anim12i.mm"
include "ancoms.mm"
include "3adant3.mm"
include "simp3.mm"
include "df-3an.mm"
include "sylanbrc.mm"
include "lemul2a.mm"
include "ex.mm"
include "syl.mm"
include "wb.mm"
include "lerec.mm"
include "wceq.mm"
include "cc.mm"
include "recn.mm"
include "adantr.mm"
include "jca.mm"
include "3anass.mm"
include "sylibr.mm"
include "divrec.mm"
include "3adant1.mm"
include "3adant2.mm"
include "breq12d.mm"
include "3imtr4d.mm"

theorem lediv2aALT
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. RR /\ 0 < A ) /\ ( B e. RR /\ 0 < B ) /\ ( C e. RR /\ 0 <_ C ) ) -> ( A <_ B -> ( C / B ) <_ ( C / A ) ) )

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
    cle
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
    @9
    @10
    cr
    wcel
    #
    @11
    cr
    wcel
    #
    @8
    w3a
    #
    @12
    @15
    wi
    @9
    @19
    @20
    wa
    #
    @8
    @21
    @2
    @5
    @22
    @8
    @5
    @2
    @22
    @5
    @19
    @2
    @20
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
    @0
    @1
    cA
    cc0
    wne
    #
    @20
    cA
    gt0ne0
    #
    cA
    rereccl
    syldan
    anim12i
    ancoms
    3adant3
    @2
    @5
    @8
    simp3
    @19
    @20
    @8
    df-3an
    sylanbrc
    @21
    @12
    @15
    @10
    @11
    cC
    lemul2a
    ex
    syl
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
    @9
    @17
    @13
    @18
    @14
    cle
    @5
    @8
    @17
    @13
    wceq
    #
    @2
    @8
    @5
    @27
    @8
    @5
    wa
    #
    cC
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @23
    w3a
    #
    @27
    @28
    @29
    @30
    @23
    wa
    #
    wa
    @31
    @8
    @29
    @5
    @32
    @6
    @29
    @7
    cC
    recn
    adantr
    #
    @5
    @30
    @23
    @3
    @30
    @4
    cB
    recn
    adantr
    @24
    jca
    anim12i
    @29
    @30
    @23
    3anass
    sylibr
    cC
    cB
    divrec
    syl
    ancoms
    3adant1
    @2
    @8
    @18
    @14
    wceq
    #
    @5
    @8
    @2
    @34
    @8
    @2
    wa
    #
    @29
    cA
    cc
    wcel
    #
    @25
    w3a
    #
    @34
    @35
    @29
    @36
    @25
    wa
    #
    wa
    @37
    @8
    @29
    @2
    @38
    @33
    @2
    @36
    @25
    @0
    @36
    @1
    cA
    recn
    adantr
    @26
    jca
    anim12i
    @29
    @36
    @25
    3anass
    sylibr
    cC
    cA
    divrec
    syl
    ancoms
    3adant2
    breq12d
    3imtr4d
end
