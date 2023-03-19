include "cvv.mm"
include "wcel.mm"
include "cima.mm"
include "imaexg.mm"
include "ax-mp.mm"

theorem imaex
  let cA: class A
  let cB: class B
  assume imaex.1: |- A e. _V


  assert |- ( A " B ) e. _V

  proof
    cA
    cvv
    wcel
    cA
    cB
    cima
    cvv
    wcel
    imaex.1
    cA
    cB
    cvv
    imaexg
    ax-mp
end
