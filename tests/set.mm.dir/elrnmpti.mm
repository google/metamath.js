include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "crn.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "rgenw.mm"
include "elrnmptg.mm"
include "ax-mp.mm"

theorem elrnmpti
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vy: setvar y
  let vz: setvar z
  assume rnmpt.1: |- F = ( x e. A |-> B )
  assume elrnmpti.2: |- B e. _V

  disjoint C x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint x y
  disjoint x z
  disjoint C y
  disjoint C z
  assert |- ( C e. ran F <-> E. x e. A C = B )

  proof
    cB
    cvv
    wcel
    #
    vx
    cA
    wral
    cC
    cF
    crn
    wcel
    cC
    cB
    wceq
    vx
    cA
    wrex
    wb
    @0
    vx
    cA
    elrnmpti.2
    rgenw
    vx
    cA
    cB
    cC
    cF
    cvv
    rnmpt.1
    elrnmptg
    ax-mp
end
