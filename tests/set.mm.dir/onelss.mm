include "con0.mm"
include "wcel.mm"
include "word.mm"
include "wss.mm"
include "wi.mm"
include "eloni.mm"
include "ordelss.mm"
include "ex.mm"
include "syl.mm"

theorem onelss
  let cA: class A
  let cB: class B


  assert |- ( A e. On -> ( B e. A -> B C_ A ) )

  proof
    cA
    con0
    wcel
    cA
    word
    #
    cB
    cA
    wcel
    #
    cB
    cA
    wss
    #
    wi
    cA
    eloni
    @0
    @1
    @2
    cA
    cB
    ordelss
    ex
    syl
end
