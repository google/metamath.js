include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cr.mm"
include "wcel.mm"
include "rerecclzi.mm"
include "ax-mp.mm"

theorem rereccli
  let cA: class A
  assume redivcl.1: |- A e. RR
  assume rereccl.2: |- A =/= 0


  assert |- ( 1 / A ) e. RR

  proof
    cA
    cc0
    wne
    c1
    cA
    cdiv
    co
    cr
    wcel
    rereccl.2
    cA
    redivcl.1
    rerecclzi
    ax-mp
end
