include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "cr.mm"
include "wcel.mm"
include "redivclzi.mm"
include "ax-mp.mm"

theorem redivcli
  let cA: class A
  let cB: class B
  assume redivcl.1: |- A e. RR
  assume redivcl.2: |- B e. RR
  assume redivcl.3: |- B =/= 0


  assert |- ( A / B ) e. RR

  proof
    cB
    cc0
    wne
    cA
    cB
    cdiv
    co
    cr
    wcel
    redivcl.3
    cA
    cB
    redivcl.1
    redivcl.2
    redivclzi
    ax-mp
end
