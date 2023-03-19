include "cdm.mm"
include "cvv.mm"
include "wcel.mm"
include "crab.mm"
include "dmmpt.mm"
include "ssrab2.mm"
include "eqsstri.mm"

theorem dmmptss
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vy: setvar y
  let cC: class C
  let cV: class V
  assume dmmpt.1: |- F = ( x e. A |-> B )

  disjoint A x
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint A y
  disjoint B y
  disjoint F y
  disjoint V x
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
    dmmpt.1
    dmmpt
    @0
    vx
    cA
    ssrab2
    eqsstri
end
