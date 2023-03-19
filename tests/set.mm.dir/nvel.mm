include "cvv.mm"
include "wcel.mm"
include "vprc.mm"
include "elex.mm"
include "mto.mm"

theorem nvel
  let cA: class A


  assert |- -. _V e. A

  proof
    cvv
    cA
    wcel
    cvv
    cvv
    wcel
    vprc
    cvv
    cA
    elex
    mto
end
