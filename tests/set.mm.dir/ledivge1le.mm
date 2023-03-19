include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "wi.mm"
include "wb.mm"
include "divle1le.mm"
include "adantr.mm"
include "rerpdivcl.mm"
include "1red.mm"
include "rpre.mm"
include "adantl.mm"
include "letr.mm"
include "syl3anc.mm"
include "expd.mm"
include "sylbird.mm"
include "com23.mm"
include "expimpd.mm"
include "ex.mm"
include "3imp1.mm"
include "cc0.mm"
include "clt.mm"
include "simp1.mm"
include "0lt1.mm"
include "0red.mm"
include "ltletr.mm"
include "mpani.mm"
include "imp.mm"
include "jca.mm"
include "3ad2ant3.mm"
include "rpregt0.mm"
include "3ad2ant2.mm"
include "3jca.mm"
include "lediv23.mm"
include "syl.mm"
include "mpbird.mm"

theorem ledivge1le
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR+ /\ ( C e. RR+ /\ 1 <_ C ) ) -> ( A <_ B -> ( A / C ) <_ B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    crp
    wcel
    #
    cC
    crp
    wcel
    #
    c1
    cC
    cle
    wbr
    #
    wa
    #
    w3a
    #
    cA
    cB
    cle
    wbr
    #
    cA
    cC
    cdiv
    co
    cB
    cle
    wbr
    #
    @5
    @6
    wa
    #
    @7
    cA
    cB
    cdiv
    co
    #
    cC
    cle
    wbr
    #
    @0
    @1
    @4
    @6
    @10
    @0
    @1
    @4
    @6
    @10
    wi
    #
    wi
    @0
    @1
    wa
    #
    @2
    @3
    @11
    @12
    @2
    wa
    #
    @6
    @3
    @10
    @13
    @6
    @9
    c1
    cle
    wbr
    #
    @3
    @10
    wi
    @12
    @14
    @6
    wb
    @2
    cA
    cB
    divle1le
    adantr
    @13
    @14
    @3
    @10
    @13
    @9
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    @14
    @3
    wa
    @10
    wi
    @12
    @15
    @2
    cA
    cB
    rerpdivcl
    adantr
    @13
    1red
    @2
    @17
    @12
    cC
    rpre
    #
    adantl
    @9
    c1
    cC
    letr
    syl3anc
    expd
    sylbird
    com23
    expimpd
    ex
    3imp1
    @8
    @0
    @17
    cc0
    cC
    clt
    wbr
    #
    wa
    #
    cB
    cr
    wcel
    cc0
    cB
    clt
    wbr
    wa
    #
    w3a
    #
    @7
    @10
    wb
    @5
    @22
    @6
    @5
    @0
    @20
    @21
    @0
    @1
    @4
    simp1
    @4
    @0
    @20
    @1
    @4
    @17
    @19
    @2
    @17
    @3
    @18
    adantr
    @2
    @3
    @19
    @2
    cc0
    c1
    clt
    wbr
    #
    @3
    @19
    0lt1
    @2
    cc0
    cr
    wcel
    @16
    @17
    @23
    @3
    wa
    @19
    wi
    @2
    0red
    @2
    1red
    @18
    cc0
    c1
    cC
    ltletr
    syl3anc
    mpani
    imp
    jca
    3ad2ant3
    @1
    @0
    @21
    @4
    cB
    rpregt0
    3ad2ant2
    3jca
    adantr
    cA
    cC
    cB
    lediv23
    syl
    mpbird
    ex
end
