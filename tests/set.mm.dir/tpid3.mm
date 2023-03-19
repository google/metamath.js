include "cvv.mm"
include "wcel.mm"
include "ctp.mm"
include "tpid3g.mm"
include "ax-mp.mm"

theorem tpid3
  let cA: class A
  let cB: class B
  let cC: class C
  assume tpid3.1: |- C e. _V


  assert |- C e. { A , B , C }

  proof
    cC
    cvv
    wcel
    cC
    cA
    cB
    cC
    ctp
    wcel
    tpid3.1
    cC
    cvv
    cA
    cB
    tpid3g
    ax-mp
end
