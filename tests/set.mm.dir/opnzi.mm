include "cop.mm"
include "c0.mm"
include "wne.mm"
include "cvv.mm"
include "wcel.mm"
include "opnz.mm"
include "mpbir2an.mm"

theorem opnzi
  let cA: class A
  let cB: class B
  assume opth1.1: |- A e. _V
  assume opth1.2: |- B e. _V


  assert |- <. A , B >. =/= (/)

  proof
    cA
    cB
    cop
    c0
    wne
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    opth1.1
    opth1.2
    cA
    cB
    opnz
    mpbir2an
end
