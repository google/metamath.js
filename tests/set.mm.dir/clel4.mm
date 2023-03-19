include "cv.mm"
include "wceq.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "eleq2.mm"
include "ceqsalv.mm"
include "bicomi.mm"

theorem clel4
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume clel4.1: |- B e. _V

  disjoint A x
  disjoint B x
  assert |- ( A e. B <-> A. x ( x = B -> A e. x ) )

  proof
    vx
    cv
    #
    cB
    wceq
    cA
    @0
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
    cB
    clel4.1
    @0
    cB
    cA
    eleq2
    ceqsalv
    bicomi
end
