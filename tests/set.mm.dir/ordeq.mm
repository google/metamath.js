include "wceq.mm"
include "wtr.mm"
include "cep.mm"
include "wwe.mm"
include "wa.mm"
include "word.mm"
include "treq.mm"
include "weeq2.mm"
include "anbi12d.mm"
include "df-ord.mm"
include "3bitr4g.mm"

theorem ordeq
  let cA: class A
  let cB: class B


  assert |- ( A = B -> ( Ord A <-> Ord B ) )

  proof
    cA
    cB
    wceq
    #
    cA
    wtr
    #
    cA
    cep
    wwe
    #
    wa
    cB
    wtr
    #
    cB
    cep
    wwe
    #
    wa
    cA
    word
    cB
    word
    @0
    @1
    @3
    @2
    @4
    cA
    cB
    treq
    cA
    cB
    cep
    weeq2
    anbi12d
    cA
    df-ord
    cB
    df-ord
    3bitr4g
end
