include "c0.mm"
include "wne.mm"
include "cint.mm"
include "cuni.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "wrex.mm"
include "r19.2z.mm"
include "ex.mm"
include "vex.mm"
include "elint2.mm"
include "eluni2.mm"
include "3imtr4g.mm"
include "ssrdv.mm"

theorem intssuni
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let wph: wff ph


  assert |- ( A =/= (/) -> |^| A C_ U. A )

  proof
    cA
    c0
    wne
    #
    vx
    cA
    cint
    #
    cA
    cuni
    #
    @0
    vx
    cv
    #
    vy
    cv
    wcel
    #
    vy
    cA
    wral
    #
    @4
    vy
    cA
    wrex
    #
    @3
    @1
    wcel
    @3
    @2
    wcel
    @0
    @5
    @6
    @4
    vy
    cA
    r19.2z
    ex
    vy
    @3
    cA
    vx
    vex
    elint2
    vy
    @3
    cA
    eluni2
    3imtr4g
    ssrdv
end
