include "cint.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "dfss3.mm"
include "vex.mm"
include "elint2.mm"
include "ralbii.mm"
include "ralcom.mm"
include "bitr4i.mm"
include "3bitri.mm"

theorem ssint
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let wph: wff ph

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint ph y
  assert |- ( A C_ |^| B <-> A. x e. B A C_ x )

  proof
    cA
    cB
    cint
    #
    wss
    vy
    cv
    #
    @0
    wcel
    #
    vy
    cA
    wral
    @1
    vx
    cv
    #
    wcel
    #
    vx
    cB
    wral
    #
    vy
    cA
    wral
    #
    cA
    @3
    wss
    #
    vx
    cB
    wral
    #
    vy
    cA
    @0
    dfss3
    @2
    @5
    vy
    cA
    vx
    @1
    cB
    vy
    vex
    elint2
    ralbii
    @6
    @4
    vy
    cA
    wral
    #
    vx
    cB
    wral
    @8
    @4
    vy
    vx
    cA
    cB
    ralcom
    @7
    @9
    vx
    cB
    vy
    cA
    @3
    dfss3
    ralbii
    bitr4i
    3bitri
end
