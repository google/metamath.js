include "csh.mm"
include "wcel.mm"
include "chil.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "shss.mm"
include "ocss.mm"
include "syl.mm"

theorem shocss
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cH: class H
  let cB: class B


  assert |- ( A e. SH -> ( _|_ ` A ) C_ ~H )

  proof
    cA
    csh
    wcel
    cA
    chil
    wss
    cA
    cort
    cfv
    chil
    wss
    cA
    shss
    cA
    ocss
    syl
end
