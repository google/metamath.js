include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "csb.mm"
include "cv.mm"
include "wsbc.mm"
include "cab.mm"
include "c0.mm"
include "df-csb.mm"
include "wal.mm"
include "wceq.mm"
include "sbcex.mm"
include "con3i.mm"
include "alrimiv.mm"
include "bj-ab0.mm"
include "syl.mm"
include "syl5eq.mm"

theorem bj-csbprc
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y


  assert |- ( -. A e. _V -> [_ A / x ]_ B = (/) )

  proof
    cA
    cvv
    wcel
    #
    wn
    #
    vx
    cA
    cB
    csb
    vy
    cv
    cB
    wcel
    #
    vx
    cA
    wsbc
    #
    vy
    cab
    #
    c0
    vx
    vy
    cA
    cB
    df-csb
    @1
    @3
    wn
    #
    vy
    wal
    @4
    c0
    wceq
    @1
    @5
    vy
    @3
    @0
    @2
    vx
    cA
    sbcex
    con3i
    alrimiv
    @3
    vy
    bj-ab0
    syl
    syl5eq
end
