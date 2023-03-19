include "cph.mm"
include "co.mm"
include "cv.mm"
include "shsel1i.mm"
include "ssriv.mm"

theorem shsub1i
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D
  assume shincl.1: |- A e. SH
  assume shincl.2: |- B e. SH


  assert |- A C_ ( A +H B )

  proof
    vx
    cA
    cA
    cB
    cph
    co
    cA
    cB
    vx
    cv
    shincl.1
    shincl.2
    shsel1i
    ssriv
end
