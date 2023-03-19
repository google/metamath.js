include "c1.mm"
include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "divdiv1.mm"
include "mp3an1.mm"

theorem recdiv2
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ B =/= 0 ) ) -> ( ( 1 / A ) / B ) = ( 1 / ( A x. B ) ) )

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
    wa
    cB
    cc
    wcel
    cB
    cc0
    wne
    wa
    c1
    cA
    cdiv
    co
    cB
    cdiv
    co
    c1
    cA
    cB
    cmul
    co
    cdiv
    co
    wceq
    ax-1cn
    c1
    cA
    cB
    divdiv1
    mp3an1
end
