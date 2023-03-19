include "wss.mm"
include "chj.mm"
include "co.mm"
include "shlej1i.mm"
include "shjcomi.mm"
include "3sstr4g.mm"

theorem shlej2i
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  assume shincl.1: |- A e. SH
  assume shincl.2: |- B e. SH
  assume shless.1: |- C e. SH


  assert |- ( A C_ B -> ( C vH A ) C_ ( C vH B ) )

  proof
    cA
    cB
    wss
    cA
    cC
    chj
    co
    cB
    cC
    chj
    co
    cC
    cA
    chj
    co
    cC
    cB
    chj
    co
    cA
    cB
    cC
    shincl.1
    shincl.2
    shless.1
    shlej1i
    cC
    cA
    shless.1
    shincl.1
    shjcomi
    cC
    cB
    shless.1
    shincl.2
    shjcomi
    3sstr4g
end
