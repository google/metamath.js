include "cv.mm"
include "csn.mm"
include "csb.mm"
include "bj-csbsnlem.mm"
include "csbeq2i.mm"
include "csbco.mm"
include "3eqtr3i.mm"

theorem bj-csbsn
  let vx: setvar x
  let cA: class A
  let vy: setvar y


  assert |- [_ A / x ]_ { x } = { A }

  proof
    vy
    cA
    vx
    vy
    cv
    #
    vx
    cv
    csn
    #
    csb
    #
    csb
    vy
    cA
    @0
    csn
    #
    csb
    vx
    cA
    @1
    csb
    cA
    csn
    vy
    cA
    @2
    @3
    vx
    @0
    bj-csbsnlem
    csbeq2i
    vx
    vy
    cA
    @1
    csbco
    vy
    cA
    bj-csbsnlem
    3eqtr3i
end
