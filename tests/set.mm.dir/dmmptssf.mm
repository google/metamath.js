include "cdm.mm"
include "cvv.mm"
include "wcel.mm"
include "crab.mm"
include "dmmpt.mm"
include "ssrab2f.mm"
include "eqsstri.mm"

theorem dmmptssf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  assume dmmptssf.1: |- F/_ x A
  assume dmmptssf.2: |- F = ( x e. A |-> B )


  assert |- dom F C_ A

  proof
    cF
    cdm
    cB
    cvv
    wcel
    #
    vx
    cA
    crab
    cA
    vx
    cA
    cB
    cF
    dmmptssf.2
    dmmpt
    @0
    vx
    cA
    dmmptssf.1
    ssrab2f
    eqsstri
end
