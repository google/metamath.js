include "csh.mm"
include "wcel.mm"
include "chil.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "shss.mm"
include "ococss.mm"
include "syl.mm"

theorem shococss
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cH: class H
  let cB: class B


  assert |- ( A e. SH -> A C_ ( _|_ ` ( _|_ ` A ) ) )

  proof
    cA
    csh
    wcel
    cA
    chil
    wss
    cA
    cA
    cort
    cfv
    cort
    cfv
    wss
    cA
    shss
    cA
    ococss
    syl
end
