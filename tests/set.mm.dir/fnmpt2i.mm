include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "cxp.mm"
include "wfn.mm"
include "rgen2w.mm"
include "fnmpt2.mm"
include "ax-mp.mm"

theorem fnmpt2i
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
  assert |- F Fn ( A X. B )

  proof
    cC
    cvv
    wcel
    #
    vy
    cB
    wral
    vx
    cA
    wral
    cF
    cA
    cB
    cxp
    wfn
    @0
    vx
    vy
    cA
    cB
    fnmpt2i.2
    rgen2w
    vx
    vy
    cA
    cB
    cC
    cF
    cvv
    fmpt2.1
    fnmpt2
    ax-mp
end
