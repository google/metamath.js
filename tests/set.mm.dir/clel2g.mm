include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "nfv.mm"
include "eleq1.mm"
include "ceqsalg.mm"
include "bicomd.mm"

theorem clel2g
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V

  disjoint A x
  disjoint B x
  assert |- ( A e. V -> ( A e. B <-> A. x ( x = A -> x e. B ) ) )

  proof
    cA
    cV
    wcel
    vx
    cv
    #
    cA
    wceq
    @0
    cB
    wcel
    #
    wi
    vx
    wal
    cA
    cB
    wcel
    #
    @1
    @2
    vx
    cA
    cV
    @2
    vx
    nfv
    @0
    cA
    cB
    eleq1
    ceqsalg
    bicomd
end
