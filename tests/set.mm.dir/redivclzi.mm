include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "redivcl.mm"
include "mp3an12.mm"

theorem redivclzi
  let cA: class A
  let cB: class B
  assume redivcl.1: |- A e. RR
  assume redivcl.2: |- B e. RR


  assert |- ( B =/= 0 -> ( A / B ) e. RR )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    cB
    cc0
    wne
    cA
    cB
    cdiv
    co
    cr
    wcel
    redivcl.1
    redivcl.2
    cA
    cB
    redivcl
    mp3an12
end
