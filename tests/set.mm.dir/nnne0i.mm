include "nnrei.mm"
include "nngt0i.mm"
include "gt0ne0ii.mm"

theorem nnne0i
  let cA: class A
  assume nngt0.1: |- A e. NN


  assert |- A =/= 0

  proof
    cA
    cA
    nngt0.1
    nnrei
    cA
    nngt0.1
    nngt0i
    gt0ne0ii
end
