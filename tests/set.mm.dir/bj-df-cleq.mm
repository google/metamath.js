include "dfcleq.mm"

theorem bj-df-cleq
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  assume bj-df-cleq.1: |- A. u A. v ( u = v <-> A. w ( w e. u <-> w e. v ) )

  disjoint u v
  disjoint u w
  disjoint u x
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint A v
  disjoint w x
  disjoint A w
  disjoint A x
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B x
  assert |- ( A = B <-> A. x ( x e. A <-> x e. B ) )

  proof
    vx
    cA
    cB
    dfcleq
end
