include "chj.mm"
include "co.mm"
include "shjcli.mm"
include "chshii.mm"

theorem shjshcli
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


  assert |- ( A vH B ) e. SH

  proof
    cA
    cB
    chj
    co
    cA
    cB
    shincl.1
    shincl.2
    shjcli
    chshii
end
