include "cuni.mm"
include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "word.mm"
include "wcel.mm"
include "df-ne.mm"
include "con0.mm"
include "csuc.mm"
include "wo.mm"
include "ordeleqon.mm"
include "unon.mm"
include "eqcomi.mm"
include "id.mm"
include "unieq.mm"
include "3eqtr4a.mm"
include "orim2i.mm"
include "sylbi.mm"
include "orcomd.mm"
include "ord.mm"
include "orduniorsuc.mm"
include "wi.mm"
include "onuni.mm"
include "eleq1a.mm"
include "3syl.mm"
include "syl6c.mm"
include "syl5bi.mm"

theorem ordtoplem
  let cA: class A
  let cS: class S
  assume ordtoplem.1: |- ( U. A e. On -> suc U. A e. S )


  assert |- ( Ord A -> ( A =/= U. A -> A e. S ) )

  proof
    cA
    cA
    cuni
    #
    wne
    cA
    @0
    wceq
    #
    wn
    #
    cA
    word
    #
    cA
    cS
    wcel
    #
    cA
    @0
    df-ne
    @3
    @2
    cA
    con0
    wcel
    #
    cA
    @0
    csuc
    #
    wceq
    #
    @4
    @3
    @1
    @5
    @3
    @5
    @1
    @3
    @5
    cA
    con0
    wceq
    #
    wo
    @5
    @1
    wo
    cA
    ordeleqon
    @8
    @1
    @5
    @8
    con0
    con0
    cuni
    #
    cA
    @0
    @9
    con0
    unon
    eqcomi
    @8
    id
    cA
    con0
    unieq
    3eqtr4a
    orim2i
    sylbi
    orcomd
    ord
    @3
    @1
    @7
    cA
    orduniorsuc
    ord
    @5
    @0
    con0
    wcel
    @6
    cS
    wcel
    @7
    @4
    wi
    cA
    onuni
    ordtoplem.1
    @6
    cS
    cA
    eleq1a
    3syl
    syl6c
    syl5bi
end
