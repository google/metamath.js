include "cvv.mm"
include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "wne.mm"
include "wa.mm"
include "wb.mm"
include "map0g.mm"
include "mp2an.mm"

theorem map0
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vy: setvar y
  assume map0.1: |- A e. _V
  assume map0.2: |- B e. _V


  assert |- ( ( A ^m B ) = (/) <-> ( A = (/) /\ B =/= (/) ) )

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cA
    cB
    cmap
    co
    c0
    wceq
    cA
    c0
    wceq
    cB
    c0
    wne
    wa
    wb
    map0.1
    map0.2
    cA
    cB
    cvv
    cvv
    map0g
    mp2an
end
