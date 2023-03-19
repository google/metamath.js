include "csh.mm"
include "wcel.mm"
include "chil.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "shss.mm"
include "ocsh.mm"
include "syl.mm"

theorem shocsh
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cH: class H
  let cB: class B


  assert |- ( A e. SH -> ( _|_ ` A ) e. SH )

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
    csh
    wcel
    cA
    shss
    cA
    ocsh
    syl
end
