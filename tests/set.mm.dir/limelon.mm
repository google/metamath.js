include "wcel.mm"
include "wlim.mm"
include "con0.mm"
include "word.mm"
include "limord.mm"
include "elong.mm"
include "syl5ibr.mm"
include "imp.mm"

theorem limelon
  let cA: class A
  let cB: class B


  assert |- ( ( A e. B /\ Lim A ) -> A e. On )

  proof
    cA
    cB
    wcel
    #
    cA
    wlim
    #
    cA
    con0
    wcel
    #
    @1
    @2
    @0
    cA
    word
    cA
    limord
    cA
    cB
    elong
    syl5ibr
    imp
end
