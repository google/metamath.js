include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wral.mm"
include "wi.mm"
include "wal.mm"
include "disj.mm"
include "df-ral.mm"
include "bitri.mm"

theorem disj1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint A x
  disjoint B x
  disjoint C x
  assert |- ( ( A i^i B ) = (/) <-> A. x ( x e. A -> -. x e. B ) )

  proof
    cA
    cB
    cin
    c0
    wceq
    vx
    cv
    #
    cB
    wcel
    wn
    #
    vx
    cA
    wral
    @0
    cA
    wcel
    @1
    wi
    vx
    wal
    vx
    cA
    cB
    disj
    @1
    vx
    cA
    df-ral
    bitri
end
