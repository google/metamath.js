include "cint.mm"
include "wcel.mm"
include "cv.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "elint.mm"
include "df-ral.mm"
include "bitr4i.mm"

theorem elint2
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume elint2.1: |- A e. _V

  disjoint A x
  disjoint B x
  assert |- ( A e. |^| B <-> A. x e. B A e. x )

  proof
    cA
    cB
    cint
    wcel
    vx
    cv
    #
    cB
    wcel
    cA
    @0
    wcel
    #
    wi
    vx
    wal
    @1
    vx
    cB
    wral
    vx
    cA
    cB
    elint2.1
    elint
    @1
    vx
    cB
    df-ral
    bitr4i
end
