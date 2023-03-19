include "con0.mm"
include "wcel.mm"
include "w3a.mm"
include "wo.mm"
include "wn.mm"
include "coa.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "oaord.mm"
include "3comr.mm"
include "3com13.mm"
include "orbi12d.mm"
include "notbid.mm"
include "word.mm"
include "eloni.mm"
include "ordtri3.mm"
include "syl2an.mm"
include "3adant1.mm"
include "wa.mm"
include "oacl.mm"
include "syl.mm"
include "3impdi.mm"
include "3bitr4rd.mm"

theorem oacan
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. On /\ B e. On /\ C e. On ) -> ( ( A +o B ) = ( A +o C ) <-> B = C ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    cC
    con0
    wcel
    #
    w3a
    #
    cB
    cC
    wcel
    #
    cC
    cB
    wcel
    #
    wo
    #
    wn
    #
    cA
    cB
    coa
    co
    #
    cA
    cC
    coa
    co
    #
    wcel
    #
    @9
    @8
    wcel
    #
    wo
    #
    wn
    #
    cB
    cC
    wceq
    #
    @8
    @9
    wceq
    #
    @3
    @6
    @12
    @3
    @4
    @10
    @5
    @11
    @1
    @2
    @0
    @4
    @10
    wb
    cB
    cC
    cA
    oaord
    3comr
    @2
    @1
    @0
    @5
    @11
    wb
    cC
    cB
    cA
    oaord
    3com13
    orbi12d
    notbid
    @1
    @2
    @14
    @7
    wb
    #
    @0
    @1
    cB
    word
    cC
    word
    @16
    @2
    cB
    eloni
    cC
    eloni
    cB
    cC
    ordtri3
    syl2an
    3adant1
    @0
    @1
    @2
    @15
    @13
    wb
    #
    @0
    @1
    wa
    #
    @8
    word
    #
    @9
    word
    #
    @17
    @0
    @2
    wa
    #
    @18
    @8
    con0
    wcel
    @19
    cA
    cB
    oacl
    @8
    eloni
    syl
    @21
    @9
    con0
    wcel
    @20
    cA
    cC
    oacl
    @9
    eloni
    syl
    @8
    @9
    ordtri3
    syl2an
    3impdi
    3bitr4rd
end
