include "wfal.mm"
include "empty-surprise.mm"

theorem empty-surprise2
  let vx: setvar x
  let cA: class A
  let vk: setvar k
  assume empty-surprise2.1: |- -. E. x x e. A


  assert |- A. x e. A F.

  proof
    wfal
    vx
    cA
    empty-surprise2.1
    empty-surprise
end
