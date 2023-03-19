include "csh.mm"
include "wcel.mm"
include "cort.mm"
include "cfv.mm"
include "c0v.mm"
include "shocsh.mm"
include "sh0.mm"
include "syl.mm"

theorem oc0
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B


  assert |- ( H e. SH -> 0h e. ( _|_ ` H ) )

  proof
    cH
    csh
    wcel
    cH
    cort
    cfv
    #
    csh
    wcel
    c0v
    @0
    wcel
    cH
    shocsh
    @0
    sh0
    syl
end
