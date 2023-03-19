include "con0.mm"
include "wcel.mm"
include "word.mm"
include "cpw.mm"
include "cin.mm"
include "csuc.mm"
include "wceq.mm"
include "eloni.mm"
include "ordpwsuc.mm"
include "syl.mm"

theorem onpwsuc
  let cA: class A
  let vx: setvar x


  assert |- ( A e. On -> ( ~P A i^i On ) = suc A )

  proof
    cA
    con0
    wcel
    cA
    word
    cA
    cpw
    con0
    cin
    cA
    csuc
    wceq
    cA
    eloni
    cA
    ordpwsuc
    syl
end
