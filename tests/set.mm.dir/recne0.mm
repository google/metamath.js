include "c1.mm"
include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "ax-1cn.mm"
include "ax-1ne0.mm"
include "divne0.mm"
include "mpanl12.mm"

theorem recne0
  let cA: class A


  assert |- ( ( A e. CC /\ A =/= 0 ) -> ( 1 / A ) =/= 0 )

  proof
    c1
    cc
    wcel
    c1
    cc0
    wne
    cA
    cc
    wcel
    cA
    cc0
    wne
    wa
    c1
    cA
    cdiv
    co
    cc0
    wne
    ax-1cn
    ax-1ne0
    c1
    cA
    divne0
    mpanl12
end
