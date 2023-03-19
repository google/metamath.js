include "cvv.mm"
include "wcel.mm"
include "ccom.mm"
include "coexg.mm"
include "mp2an.mm"

theorem coex
  let cA: class A
  let cB: class B
  assume coex.1: |- A e. _V
  assume coex.2: |- B e. _V


  assert |- ( A o. B ) e. _V

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cA
    cB
    ccom
    cvv
    wcel
    coex.1
    coex.2
    cA
    cB
    cvv
    cvv
    coexg
    mp2an
end
