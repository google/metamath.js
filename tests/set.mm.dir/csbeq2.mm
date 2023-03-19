include "wceq.mm"
include "wal.mm"
include "cv.mm"
include "wcel.mm"
include "wsbc.mm"
include "cab.mm"
include "csb.mm"
include "wb.mm"
include "eleq2.mm"
include "alimi.mm"
include "sbcbi2.mm"
include "syl.mm"
include "abbidv.mm"
include "df-csb.mm"
include "3eqtr4g.mm"

theorem csbeq2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y


  assert |- ( A. x B = C -> [_ A / x ]_ B = [_ A / x ]_ C )

  proof
    cB
    cC
    wceq
    #
    vx
    wal
    #
    vy
    cv
    #
    cB
    wcel
    #
    vx
    cA
    wsbc
    #
    vy
    cab
    @2
    cC
    wcel
    #
    vx
    cA
    wsbc
    #
    vy
    cab
    vx
    cA
    cB
    csb
    vx
    cA
    cC
    csb
    @1
    @4
    @6
    vy
    @1
    @3
    @5
    wb
    #
    vx
    wal
    @4
    @6
    wb
    @0
    @7
    vx
    cB
    cC
    @2
    eleq2
    alimi
    @3
    @5
    vx
    cA
    sbcbi2
    syl
    abbidv
    vx
    vy
    cA
    cB
    df-csb
    vx
    vy
    cA
    cC
    df-csb
    3eqtr4g
end
