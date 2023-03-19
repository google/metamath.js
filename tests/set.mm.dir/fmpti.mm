include "wcel.mm"
include "wral.mm"
include "wf.mm"
include "rgen.mm"
include "fmpt.mm"
include "mpbi.mm"

theorem fmpti
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vy: setvar y
  let vz: setvar z
  assume fmpt.1: |- F = ( x e. A |-> C )
  assume fmpti.2: |- ( x e. A -> C e. B )

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C y
  disjoint C z
  disjoint F y
  disjoint F z
  assert |- F : A --> B

  proof
    cC
    cB
    wcel
    #
    vx
    cA
    wral
    cA
    cB
    cF
    wf
    @0
    vx
    cA
    fmpti.2
    rgen
    vx
    cA
    cB
    cC
    cF
    fmpt.1
    fmpt
    mpbi
end
