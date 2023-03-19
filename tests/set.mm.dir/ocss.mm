include "chil.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "csh.mm"
include "wcel.mm"
include "ocsh.mm"
include "shss.mm"
include "syl.mm"

theorem ocss
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cH: class H
  let cB: class B


  assert |- ( A C_ ~H -> ( _|_ ` A ) C_ ~H )

  proof
    cA
    chil
    wss
    cA
    cort
    cfv
    #
    csh
    wcel
    @0
    chil
    wss
    cA
    ocsh
    @0
    shss
    syl
end
