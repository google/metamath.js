include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "weq.mm"
include "wb.mm"
include "wal.mm"
include "cab.mm"
include "cuni.mm"
include "wa.mm"
include "wex.mm"
include "fv2.mm"
include "eleq2i.mm"
include "eluniab.mm"
include "bitri.mm"

theorem elfv
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F

  disjoint A x
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  assert |- ( A e. ( F ` B ) <-> E. x ( A e. x /\ A. y ( B F y <-> y = x ) ) )

  proof
    cA
    cB
    cF
    cfv
    #
    wcel
    cA
    cB
    vy
    cv
    cF
    wbr
    vy
    vx
    weq
    wb
    vy
    wal
    #
    vx
    cab
    cuni
    #
    wcel
    cA
    vx
    cv
    wcel
    @1
    wa
    vx
    wex
    @0
    @2
    cA
    vx
    vy
    cB
    cF
    fv2
    eleq2i
    @1
    vx
    cA
    eluniab
    bitri
end
