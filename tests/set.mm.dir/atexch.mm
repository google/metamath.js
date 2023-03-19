include "cch.mm"
include "wcel.mm"
include "cat.mm"
include "w3a.mm"
include "chj.mm"
include "co.mm"
include "wss.mm"
include "cin.mm"
include "c0h.mm"
include "wceq.mm"
include "wa.mm"
include "atelch.mm"
include "chub2.mm"
include "ancoms.mm"
include "sylan2.mm"
include "3adant2.mm"
include "adantr.mm"
include "wpss.mm"
include "wi.mm"
include "ccv.mm"
include "wbr.mm"
include "cvp.mm"
include "chjcl.mm"
include "cvpss.mm"
include "syldan.mm"
include "sylbid.mm"
include "3adant3.mm"
include "adantld.mm"
include "id.mm"
include "chub1.mm"
include "a1d.mm"
include "ancrd.mm"
include "wb.mm"
include "chlub.mm"
include "syld3an3.mm"
include "sylibd.mm"
include "syl3an.mm"
include "adantrd.mm"
include "jcad.mm"
include "imp.mm"
include "simp1.mm"
include "3jca.mm"
include "anim12d.mm"
include "ancomsd.mm"
include "psssstr.mm"
include "syl6.mm"
include "chcv2.mm"
include "cvnbtwn2.mm"
include "sylsyld.mm"
include "mpd.mm"
include "sseqtr4d.mm"
include "ex.mm"

theorem atexch
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CH /\ B e. HAtoms /\ C e. HAtoms ) -> ( ( B C_ ( A vH C ) /\ ( A i^i B ) = 0H ) -> C C_ ( A vH B ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cat
    wcel
    #
    cC
    cat
    wcel
    #
    w3a
    #
    cB
    cA
    cC
    chj
    co
    #
    wss
    #
    cA
    cB
    cin
    c0h
    wceq
    #
    wa
    #
    cC
    cA
    cB
    chj
    co
    #
    wss
    @3
    @7
    wa
    #
    cC
    @4
    @8
    @3
    cC
    @4
    wss
    #
    @7
    @0
    @2
    @10
    @1
    @2
    @0
    cC
    cch
    wcel
    #
    @10
    cC
    atelch
    #
    @11
    @0
    @10
    cC
    cA
    chub2
    ancoms
    sylan2
    3adant2
    adantr
    @9
    cA
    @8
    wpss
    #
    @8
    @4
    wss
    #
    wa
    #
    @8
    @4
    wceq
    #
    @3
    @7
    @15
    @3
    @7
    @13
    @14
    @3
    @6
    @13
    @5
    @0
    @1
    @6
    @13
    wi
    @2
    @0
    @1
    wa
    @6
    cA
    @8
    ccv
    wbr
    #
    @13
    cA
    cB
    cvp
    @0
    @1
    @8
    cch
    wcel
    #
    @17
    @13
    wi
    @1
    @0
    cB
    cch
    wcel
    #
    @18
    cB
    atelch
    #
    cA
    cB
    chjcl
    #
    sylan2
    cA
    @8
    cvpss
    syldan
    sylbid
    3adant3
    #
    adantld
    @3
    @5
    @14
    @6
    @0
    @0
    @1
    @19
    @2
    @11
    @5
    @14
    wi
    @0
    id
    #
    @20
    @12
    @0
    @19
    @11
    w3a
    #
    @5
    cA
    @4
    wss
    #
    @5
    wa
    #
    @14
    @24
    @5
    @25
    @24
    @25
    @5
    @0
    @11
    @25
    @19
    cA
    cC
    chub1
    3adant2
    a1d
    ancrd
    @0
    @19
    @11
    @4
    cch
    wcel
    #
    @26
    @14
    wb
    @0
    @11
    @27
    @19
    cA
    cC
    chjcl
    3adant2
    #
    cA
    cB
    @4
    chlub
    syld3an3
    sylibd
    syl3an
    #
    adantrd
    jcad
    imp
    @3
    @7
    @15
    @16
    wi
    #
    @3
    @0
    @27
    @18
    w3a
    #
    @7
    cA
    @4
    ccv
    wbr
    #
    @30
    @0
    @0
    @1
    @19
    @2
    @11
    @31
    @23
    @20
    @12
    @24
    @0
    @27
    @18
    @0
    @19
    @11
    simp1
    @28
    @0
    @19
    @18
    @11
    @21
    3adant3
    3jca
    syl3an
    @3
    @7
    cA
    @4
    wpss
    #
    @32
    @3
    @7
    @15
    @33
    @3
    @6
    @5
    @15
    @3
    @6
    @13
    @5
    @14
    @22
    @29
    anim12d
    ancomsd
    cA
    @8
    @4
    psssstr
    syl6
    @0
    @2
    @33
    @32
    wb
    @1
    cA
    cC
    chcv2
    3adant2
    sylibd
    cA
    @4
    @8
    cvnbtwn2
    sylsyld
    imp
    mpd
    sseqtr4d
    ex
end
