include "ccnfld.mm"
include "ccrg.mm"
include "wcel.mm"
include "crg.mm"
include "cncrng.mm"
include "crngring.mm"
include "ax-mp.mm"

theorem cnring
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B


  assert |- CCfld e. Ring

  proof
    ccnfld
    ccrg
    wcel
    ccnfld
    crg
    wcel
    cncrng
    ccnfld
    crngring
    ax-mp
end
