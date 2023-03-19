include "com.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "cv.mm"
include "coa.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wss.mm"
include "con0.mm"
include "wi.mm"
include "nnon.mm"
include "adantl.mm"
include "onelss.mm"
include "syl.mm"
include "nnawordex.mm"
include "sylibd.mm"
include "simplr.mm"
include "eleq2.mm"
include "syl5ibrcom.mm"
include "wb.mm"
include "peano1.mm"
include "nnaord.mm"
include "mp3an1.mm"
include "ancoms.mm"
include "nna0.mm"
include "adantr.mm"
include "eleq1d.mm"
include "bitrd.mm"
include "adantlr.mm"
include "sylibrd.mm"
include "ancrd.mm"
include "reximdva.mm"
include "ex.mm"
include "mpdd.mm"
include "biimpa.mm"
include "syl5ibcom.mm"
include "expimpd.mm"
include "rexlimdva.mm"
include "impbid.mm"

theorem nnaordex
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( ( A e. _om /\ B e. _om ) -> ( A e. B <-> E. x e. _om ( (/) e. x /\ ( A +o x ) = B ) ) )

  proof
    cA
    com
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
    wcel
    #
    c0
    vx
    cv
    #
    wcel
    #
    cA
    @4
    coa
    co
    #
    cB
    wceq
    #
    wa
    #
    vx
    com
    wrex
    #
    @2
    @3
    @7
    vx
    com
    wrex
    #
    @9
    @2
    @3
    cA
    cB
    wss
    #
    @10
    @2
    cB
    con0
    wcel
    #
    @3
    @11
    wi
    @1
    @12
    @0
    cB
    nnon
    adantl
    cB
    cA
    onelss
    syl
    vx
    cA
    cB
    nnawordex
    sylibd
    @0
    @3
    @10
    @9
    wi
    #
    wi
    @1
    @0
    @3
    @13
    @0
    @3
    wa
    #
    @7
    @8
    vx
    com
    @14
    @4
    com
    wcel
    #
    wa
    #
    @7
    @5
    @16
    @7
    cA
    @6
    wcel
    #
    @5
    @16
    @17
    @7
    @3
    @0
    @3
    @15
    simplr
    @6
    cB
    cA
    eleq2
    #
    syl5ibrcom
    @0
    @15
    @5
    @17
    wb
    @3
    @0
    @15
    wa
    #
    @5
    cA
    c0
    coa
    co
    #
    @6
    wcel
    #
    @17
    @15
    @0
    @5
    @21
    wb
    #
    c0
    com
    wcel
    @15
    @0
    @22
    peano1
    c0
    @4
    cA
    nnaord
    mp3an1
    ancoms
    @19
    @20
    cA
    @6
    @0
    @20
    cA
    wceq
    @15
    cA
    nna0
    adantr
    eleq1d
    bitrd
    #
    adantlr
    sylibrd
    ancrd
    reximdva
    ex
    adantr
    mpdd
    @0
    @9
    @3
    wi
    @1
    @0
    @8
    @3
    vx
    com
    @19
    @5
    @7
    @3
    @19
    @5
    wa
    @17
    @7
    @3
    @19
    @5
    @17
    @23
    biimpa
    @18
    syl5ibcom
    expimpd
    rexlimdva
    adantr
    impbid
end
