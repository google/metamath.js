include "chil.mm"
include "wss.mm"
include "cspn.mm"
include "cfv.mm"
include "csh.mm"
include "wcel.mm"
include "spancl.mm"
include "shel.mm"
include "sylan.mm"

theorem elspancl
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( ( A C_ ~H /\ B e. ( span ` A ) ) -> B e. ~H )

  proof
    cA
    chil
    wss
    cA
    cspn
    cfv
    #
    csh
    wcel
    cB
    @0
    wcel
    cB
    chil
    wcel
    cA
    spancl
    cB
    @0
    shel
    sylan
end
