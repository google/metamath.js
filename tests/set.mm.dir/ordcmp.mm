include "word.mm"
include "ccmp.mm"
include "wcel.mm"
include "cuni.mm"
include "wceq.mm"
include "c1o.mm"
include "wi.mm"
include "c0.mm"
include "csn.mm"
include "wss.mm"
include "wlim.mm"
include "wo.mm"
include "orduni.mm"
include "unizlim.mm"
include "uni0b.mm"
include "orbi1i.mm"
include "syl6bb.mm"
include "biimpd.mm"
include "syl.mm"
include "sssn.mm"
include "ctop.mm"
include "0ntop.mm"
include "cmptop.mm"
include "mto.mm"
include "eleq1.mm"
include "mtbiri.mm"
include "pm2.21d.mm"
include "id.mm"
include "df1o2.mm"
include "syl6eqr.mm"
include "a1d.mm"
include "jaoi.mm"
include "sylbi.mm"
include "a1i.mm"
include "wn.mm"
include "csuc.mm"
include "wne.mm"
include "ordtop.mm"
include "necon2bd.mm"
include "con3i.mm"
include "syl6.mm"
include "a1dd.mm"
include "limsucncmp.mm"
include "notbid.mm"
include "syl5ibr.mm"
include "orduniorsuc.mm"
include "mpjaod.mm"
include "pm2.21.mm"
include "jaod.mm"
include "com23.mm"
include "syl5d.mm"
include "con0.mm"
include "ordeleqon.mm"
include "unon.mm"
include "eqcomi.mm"
include "unieqi.mm"
include "unieq.mm"
include "unieqd.mm"
include "3eqtr4a.mm"
include "orim2i.mm"
include "orcomd.mm"
include "ord.mm"
include "syl5.mm"
include "suceq.mm"
include "eqtr.mm"
include "ex.mm"
include "syl6c.mm"
include "onuni.mm"
include "onsucsuccmp.mm"
include "eleq1a.mm"
include "4syl.mm"
include "syl6eq.mm"
include "0cmp.mm"
include "syl6eqel.mm"
include "jad.mm"
include "impbid.mm"

theorem ordcmp
  let cA: class A


  assert |- ( Ord A -> ( A e. Comp <-> ( U. A = U. U. A -> A = 1o ) ) )

  proof
    cA
    word
    #
    cA
    ccmp
    wcel
    #
    cA
    cuni
    #
    @2
    cuni
    #
    wceq
    #
    cA
    c1o
    wceq
    #
    wi
    @0
    @4
    cA
    c0
    csn
    #
    wss
    #
    @2
    wlim
    #
    wo
    #
    @1
    @5
    @0
    @2
    word
    #
    @4
    @9
    wi
    cA
    orduni
    #
    @10
    @4
    @9
    @10
    @4
    @2
    c0
    wceq
    #
    @8
    wo
    @9
    @2
    unizlim
    @12
    @7
    @8
    cA
    uni0b
    orbi1i
    syl6bb
    biimpd
    syl
    @0
    @9
    @1
    @5
    @0
    @7
    @1
    @5
    wi
    #
    @8
    @7
    @13
    wi
    @0
    @7
    cA
    c0
    wceq
    #
    cA
    @6
    wceq
    #
    wo
    @13
    cA
    c0
    sssn
    @14
    @13
    @15
    @14
    @1
    @5
    @14
    @1
    c0
    ccmp
    wcel
    #
    @16
    c0
    ctop
    wcel
    0ntop
    c0
    cmptop
    mto
    cA
    c0
    ccmp
    eleq1
    mtbiri
    pm2.21d
    @15
    @5
    @1
    @15
    cA
    @6
    c1o
    @15
    id
    df1o2
    syl6eqr
    a1d
    jaoi
    sylbi
    a1i
    @0
    @8
    @1
    wn
    #
    @13
    @0
    cA
    @2
    wceq
    #
    @8
    @17
    wi
    #
    cA
    @2
    csuc
    #
    wceq
    #
    @0
    @18
    @17
    @8
    @0
    @18
    cA
    ctop
    wcel
    #
    wn
    @17
    @0
    @22
    cA
    @2
    @0
    @22
    cA
    @2
    wne
    cA
    ordtop
    biimpd
    necon2bd
    @1
    @22
    cA
    cmptop
    con3i
    syl6
    a1dd
    @21
    @19
    wi
    @0
    @8
    @17
    @21
    @20
    ccmp
    wcel
    #
    wn
    @2
    limsucncmp
    @21
    @1
    @23
    cA
    @20
    ccmp
    eleq1
    notbid
    syl5ibr
    a1i
    cA
    orduniorsuc
    #
    mpjaod
    @1
    @5
    pm2.21
    syl6
    jaod
    com23
    syl5d
    @0
    @4
    @5
    @1
    @0
    @4
    wn
    #
    cA
    con0
    wcel
    #
    cA
    @3
    csuc
    #
    csuc
    #
    wceq
    #
    @1
    @0
    @4
    @26
    @0
    @26
    @4
    @0
    @26
    cA
    con0
    wceq
    #
    wo
    @26
    @4
    wo
    cA
    ordeleqon
    @30
    @4
    @26
    @30
    con0
    cuni
    #
    @31
    cuni
    @2
    @3
    con0
    @31
    @31
    con0
    unon
    eqcomi
    unieqi
    cA
    con0
    unieq
    #
    @30
    @2
    @31
    @32
    unieqd
    3eqtr4a
    orim2i
    sylbi
    orcomd
    ord
    @0
    @25
    @21
    @20
    @28
    wceq
    #
    @29
    @25
    @18
    wn
    @0
    @21
    @18
    @4
    cA
    @2
    unieq
    con3i
    @0
    @18
    @21
    @24
    ord
    syl5
    @0
    @25
    @2
    @27
    wceq
    #
    @33
    @0
    @4
    @34
    @0
    @10
    @4
    @34
    wo
    @11
    @2
    orduniorsuc
    syl
    ord
    @2
    @27
    suceq
    syl6
    @21
    @33
    @29
    cA
    @20
    @28
    eqtr
    ex
    syl6c
    @26
    @2
    con0
    wcel
    @3
    con0
    wcel
    @28
    ccmp
    wcel
    @29
    @1
    wi
    cA
    onuni
    @2
    onuni
    @3
    onsucsuccmp
    @28
    ccmp
    cA
    eleq1a
    4syl
    syl6c
    @5
    @1
    wi
    @0
    @5
    cA
    @6
    ccmp
    @5
    cA
    c1o
    @6
    @5
    id
    df1o2
    syl6eq
    0cmp
    syl6eqel
    a1i
    jad
    impbid
end
