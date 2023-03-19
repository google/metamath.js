include "csb.mm"
include "cv.mm"
include "wcel.mm"
include "wsbc.mm"
include "sbccom.mm"
include "sbcel2.mm"
include "sbcbii.mm"
include "3bitr3i.mm"
include "eqriv.mm"

theorem csbcom
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vz: setvar z

  disjoint A y
  disjoint B x
  disjoint x y
  disjoint y z
  disjoint A z
  disjoint x z
  disjoint B z
  disjoint C z
  assert |- [_ A / x ]_ [_ B / y ]_ C = [_ B / y ]_ [_ A / x ]_ C

  proof
    vz
    vx
    cA
    vy
    cB
    cC
    csb
    #
    csb
    #
    vy
    cB
    vx
    cA
    cC
    csb
    #
    csb
    #
    vz
    cv
    #
    @0
    wcel
    #
    vx
    cA
    wsbc
    #
    @4
    @2
    wcel
    #
    vy
    cB
    wsbc
    #
    @4
    @1
    wcel
    @4
    @3
    wcel
    @4
    cC
    wcel
    #
    vy
    cB
    wsbc
    #
    vx
    cA
    wsbc
    @9
    vx
    cA
    wsbc
    #
    vy
    cB
    wsbc
    @6
    @8
    @9
    vx
    vy
    cA
    cB
    sbccom
    @10
    @5
    vx
    cA
    vy
    cB
    @4
    cC
    sbcel2
    sbcbii
    @11
    @7
    vy
    cB
    vx
    cA
    @4
    cC
    sbcel2
    sbcbii
    3bitr3i
    vx
    cA
    @4
    @0
    sbcel2
    vy
    cB
    @4
    @2
    sbcel2
    3bitr3i
    eqriv
end
