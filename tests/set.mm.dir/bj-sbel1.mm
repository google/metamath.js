include "wcel.mm"
include "wsb.mm"
include "cv.mm"
include "wsbc.mm"
include "csb.mm"
include "sbsbc.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "sbcel1g.mm"
include "ax-mp.mm"
include "bitri.mm"

theorem bj-sbel1
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint B x
  assert |- ( [ y / x ] A e. B <-> [_ y / x ]_ A e. B )

  proof
    cA
    cB
    wcel
    #
    vx
    vy
    wsb
    @0
    vx
    vy
    cv
    #
    wsbc
    #
    vx
    @1
    cA
    csb
    cB
    wcel
    #
    @0
    vx
    vy
    sbsbc
    @1
    cvv
    wcel
    @2
    @3
    wb
    vy
    vex
    vx
    @1
    cA
    cB
    cvv
    sbcel1g
    ax-mp
    bitri
end
