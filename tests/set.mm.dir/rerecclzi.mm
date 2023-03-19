include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "rereccl.mm"
include "mpan.mm"

theorem rerecclzi
  let cA: class A
  assume redivcl.1: |- A e. RR


  assert |- ( A =/= 0 -> ( 1 / A ) e. RR )

  proof
    cA
    cr
    wcel
    cA
    cc0
    wne
    c1
    cA
    cdiv
    co
    cr
    wcel
    redivcl.1
    cA
    rereccl
    mpan
end
