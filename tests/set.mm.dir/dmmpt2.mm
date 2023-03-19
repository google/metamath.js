include "cxp.mm"
include "wfn.mm"
include "cdm.mm"
include "wceq.mm"
include "fnmpt2i.mm"
include "fndm.mm"
include "ax-mp.mm"

theorem dmmpt2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cD: class D
  assume fmpt2.1: |- F = ( x e. A , y e. B |-> C )
  assume fnmpt2i.2: |- C e. _V

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint D x
  disjoint D y
  assert |- dom F = ( A X. B )

  proof
    cF
    cA
    cB
    cxp
    #
    wfn
    cF
    cdm
    @0
    wceq
    vx
    vy
    cA
    cB
    cC
    cF
    fmpt2.1
    fnmpt2i.2
    fnmpt2i
    @0
    cF
    fndm
    ax-mp
end
