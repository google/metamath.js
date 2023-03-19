include "wf.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "elmap.mm"
include "fvmpt.mm"
include "sylbir.mm"

theorem fvmptmap
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cF: class F
  assume fvmptmap.1: |- C e. _V
  assume fvmptmap.2: |- D e. _V
  assume fvmptmap.3: |- R e. _V
  assume fvmptmap.4: |- ( x = A -> B = C )
  assume fvmptmap.5: |- F = ( x e. ( R ^m D ) |-> B )

  disjoint A x
  disjoint C x
  disjoint D x
  disjoint R x
  assert |- ( A : D --> R -> ( F ` A ) = C )

  proof
    cD
    cR
    cA
    wf
    cA
    cR
    cD
    cmap
    co
    #
    wcel
    cA
    cF
    cfv
    cC
    wceq
    cR
    cD
    cA
    fvmptmap.3
    fvmptmap.2
    elmap
    vx
    cA
    cB
    cC
    @0
    cF
    fvmptmap.4
    fvmptmap.5
    fvmptmap.1
    fvmpt
    sylbir
end
