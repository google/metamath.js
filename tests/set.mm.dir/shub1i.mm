include "cph.mm"
include "co.mm"
include "chj.mm"
include "shsub1i.mm"
include "shsleji.mm"
include "sstri.mm"

theorem shub1i
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


  assert |- A C_ ( A vH B )

  proof
    cA
    cA
    cB
    cph
    co
    cA
    cB
    chj
    co
    cA
    cB
    shincl.1
    shincl.2
    shsub1i
    cA
    cB
    shincl.1
    shincl.2
    shsleji
    sstri
end
