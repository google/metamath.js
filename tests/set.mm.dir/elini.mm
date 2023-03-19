include "cin.mm"
include "wcel.mm"
include "elin.mm"
include "mpbir2an.mm"

theorem elini
  let cA: class A
  let cB: class B
  let cC: class C
  assume elini.1: |- A e. B
  assume elini.2: |- A e. C


  assert |- A e. ( B i^i C )

  proof
    cA
    cB
    cC
    cin
    wcel
    cA
    cB
    wcel
    cA
    cC
    wcel
    elini.1
    elini.2
    cA
    cB
    cC
    elin
    mpbir2an
end
