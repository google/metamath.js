include "c1.mm"
include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "ax-1cn.mm"
include "divcl.mm"
include "mp3an1.mm"

theorem reccl
  let cA: class A


  assert |- ( ( A e. CC /\ A =/= 0 ) -> ( 1 / A ) e. CC )

  proof
    c1
    cc
    wcel
    cA
    cc
    wcel
    cA
    cc0
    wne
    c1
    cA
    cdiv
    co
    cc
    wcel
    ax-1cn
    c1
    cA
    divcl
    mp3an1
end
