include "cph.mm"
include "co.mm"
include "cv.mm"
include "shsel2i.mm"
include "ssriv.mm"

theorem shsub2i
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


  assert |- A C_ ( B +H A )

  proof
    vx
    cA
    cB
    cA
    cph
    co
    cB
    cA
    vx
    cv
    shincl.2
    shincl.1
    shsel2i
    ssriv
end
