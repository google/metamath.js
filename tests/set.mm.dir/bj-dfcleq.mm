include "weq.mm"
include "wel.mm"
include "wb.mm"
include "wal.mm"
include "bj-cleqhyp.mm"
include "gen2.mm"
include "bj-df-cleq.mm"

theorem bj-dfcleq
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w

  disjoint A x
  disjoint B x
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint A v
  disjoint w x
  disjoint A w
  disjoint B u
  disjoint B v
  disjoint B w
  assert |- ( A = B <-> A. x ( x e. A <-> x e. B ) )

  proof
    vx
    vw
    vv
    vu
    cA
    cB
    vu
    vv
    weq
    vw
    vu
    wel
    vw
    vv
    wel
    wb
    vw
    wal
    wb
    vu
    vv
    vu
    vv
    vw
    bj-cleqhyp
    gen2
    bj-df-cleq
end
