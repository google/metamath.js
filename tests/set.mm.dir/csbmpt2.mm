include "wcel.mm"
include "cmpt.mm"
include "csb.mm"
include "csbmpt12.mm"
include "csbconstg.mm"
include "mpteq1d.mm"
include "eqtrd.mm"

theorem csbmpt2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cV: class V
  let cY: class Y
  let cZ: class Z
  let vz: setvar z

  disjoint A y
  disjoint V y
  disjoint Y y
  disjoint x y
  disjoint Y x
  disjoint A z
  disjoint y z
  disjoint V z
  disjoint Y z
  disjoint Z z
  disjoint x z
  assert |- ( A e. V -> [_ A / x ]_ ( y e. Y |-> Z ) = ( y e. Y |-> [_ A / x ]_ Z ) )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    vy
    cY
    cZ
    cmpt
    csb
    vy
    vx
    cA
    cY
    csb
    #
    vx
    cA
    cZ
    csb
    #
    cmpt
    vy
    cY
    @2
    cmpt
    vx
    vy
    cA
    cV
    cY
    cZ
    csbmpt12
    @0
    vy
    @1
    cY
    @2
    vx
    cA
    cY
    cV
    csbconstg
    mpteq1d
    eqtrd
end
