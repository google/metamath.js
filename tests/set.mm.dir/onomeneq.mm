include "con0.mm"
include "wcel.mm"
include "com.mm"
include "wa.mm"
include "cen.mm"
include "wbr.mm"
include "wceq.mm"
include "wss.mm"
include "wn.mm"
include "csuc.mm"
include "php5.mm"
include "ad2antlr.mm"
include "wb.mm"
include "enen1.mm"
include "adantl.mm"
include "mtbird.mm"
include "cdom.mm"
include "wi.mm"
include "peano2.mm"
include "sssucid.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "endomtr.mm"
include "sylan2.mm"
include "ancoms.mm"
include "a1d.mm"
include "adantll.mm"
include "ssel.mm"
include "com12.mm"
include "adantr.mm"
include "word.mm"
include "eloni.mm"
include "ordelsuc.mm"
include "sylibd.mm"
include "syld.mm"
include "jcad.mm"
include "sbth.mm"
include "syl6.mm"
include "mtod.mm"
include "ordom.mm"
include "ordtri1.mm"
include "sylancr.mm"
include "con2bid.mm"
include "ad2antrr.mm"
include "mpbird.mm"
include "simplr.mm"
include "jca.mm"
include "nneneq.mm"
include "biimpa.mm"
include "sylancom.mm"
include "ex.mm"
include "eqeng.mm"
include "impbid.mm"

theorem onomeneq
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ B e. _om ) -> ( A ~~ B <-> A = B ) )

  proof
    cA
    con0
    wcel
    #
    cB
    com
    wcel
    #
    wa
    #
    cA
    cB
    cen
    wbr
    #
    cA
    cB
    wceq
    #
    @2
    @3
    @4
    @2
    @3
    cA
    com
    wcel
    #
    @1
    wa
    #
    @4
    @2
    @3
    wa
    #
    @5
    @1
    @7
    @5
    com
    cA
    wss
    #
    wn
    #
    @7
    @8
    cA
    cB
    csuc
    #
    cen
    wbr
    #
    @7
    @11
    cB
    @10
    cen
    wbr
    #
    @1
    @12
    wn
    @0
    @3
    cB
    php5
    ad2antlr
    @3
    @11
    @12
    wb
    @2
    cA
    cB
    @10
    enen1
    adantl
    mtbird
    @7
    @8
    cA
    @10
    cdom
    wbr
    #
    @10
    cA
    cdom
    wbr
    #
    wa
    @11
    @7
    @8
    @13
    @14
    @1
    @3
    @8
    @13
    wi
    @0
    @1
    @3
    wa
    @13
    @8
    @3
    @1
    @13
    @1
    @3
    cB
    @10
    cdom
    wbr
    #
    @13
    @1
    @10
    com
    wcel
    cB
    @10
    wss
    @15
    cB
    peano2
    cB
    sssucid
    cB
    @10
    com
    ssdomg
    mpisyl
    cA
    cB
    @10
    endomtr
    sylan2
    ancoms
    a1d
    adantll
    @2
    @8
    @14
    wi
    #
    @3
    @1
    @0
    @16
    @1
    @0
    wa
    #
    @8
    @10
    cA
    wss
    #
    @14
    @17
    @8
    cB
    cA
    wcel
    #
    @18
    @1
    @8
    @19
    wi
    @0
    @8
    @1
    @19
    com
    cA
    cB
    ssel
    com12
    adantr
    @0
    @1
    cA
    word
    #
    @19
    @18
    wb
    cA
    eloni
    #
    cB
    cA
    com
    ordelsuc
    sylan2
    sylibd
    @0
    @18
    @14
    wi
    @1
    @10
    cA
    con0
    ssdomg
    adantl
    syld
    ancoms
    adantr
    jcad
    cA
    @10
    sbth
    syl6
    mtod
    @0
    @5
    @9
    wb
    @1
    @3
    @0
    @8
    @5
    @0
    com
    word
    @20
    @8
    @5
    wn
    wb
    ordom
    @21
    com
    cA
    ordtri1
    sylancr
    con2bid
    ad2antrr
    mpbird
    @0
    @1
    @3
    simplr
    jca
    @6
    @3
    @4
    cA
    cB
    nneneq
    biimpa
    sylancom
    ex
    @0
    @4
    @3
    wi
    @1
    cA
    cB
    con0
    eqeng
    adantr
    impbid
end
