include "wtr.mm"
include "wss.mm"
include "word.mm"
include "w3a.mm"
include "cep.mm"
include "wwe.mm"
include "wa.mm"
include "wess.mm"
include "ordwe.mm"
include "impel.mm"
include "anim2i.mm"
include "3impb.mm"
include "df-ord.mm"
include "sylibr.mm"

theorem trssord
  let cA: class A
  let cB: class B


  assert |- ( ( Tr A /\ A C_ B /\ Ord B ) -> Ord A )

  proof
    cA
    wtr
    #
    cA
    cB
    wss
    #
    cB
    word
    #
    w3a
    @0
    cA
    cep
    wwe
    #
    wa
    #
    cA
    word
    @0
    @1
    @2
    @4
    @1
    @2
    wa
    @3
    @0
    @1
    cB
    cep
    wwe
    @3
    @2
    cA
    cB
    cep
    wess
    cB
    ordwe
    impel
    anim2i
    3impb
    cA
    df-ord
    sylibr
end
