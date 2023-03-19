include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "dfss2.mm"
include "df-ral.mm"
include "bitr4i.mm"

theorem dfss3
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A C_ B <-> A. x e. A x e. B )

  proof
    cA
    cB
    wss
    vx
    cv
    #
    cA
    wcel
    @0
    cB
    wcel
    #
    wi
    vx
    wal
    @1
    vx
    cA
    wral
    vx
    cA
    cB
    dfss2
    @1
    vx
    cA
    df-ral
    bitr4i
end
