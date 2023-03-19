include "c1.mm"
include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "divcan1.mm"
include "mp3an1.mm"

theorem recid2
  let cA: class A


  assert |- ( ( A e. CC /\ A =/= 0 ) -> ( ( 1 / A ) x. A ) = 1 )

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
    cA
    cmul
    co
    c1
    wceq
    ax-1cn
    c1
    cA
    divcan1
    mp3an1
end
