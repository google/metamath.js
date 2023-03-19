include "csh.mm"
include "wcel.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "shjcom.mm"
include "mp2an.mm"

theorem shjcomi
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


  assert |- ( A vH B ) = ( B vH A )

  proof
    cA
    csh
    wcel
    cB
    csh
    wcel
    cA
    cB
    chj
    co
    cB
    cA
    chj
    co
    wceq
    shincl.1
    shincl.2
    cA
    cB
    shjcom
    mp2an
end
