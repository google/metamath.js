include "cixp.mm"
include "wcel.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wa.mm"
include "wf.mm"
include "elixp.mm"
include "ffnfv.mm"
include "bitr4i.mm"

theorem elixpconst
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  assume elixp.1: |- F e. _V

  disjoint F x
  disjoint A x
  disjoint B x
  assert |- ( F e. X_ x e. A B <-> F : A --> B )

  proof
    cF
    vx
    cA
    cB
    cixp
    wcel
    cF
    cA
    wfn
    vx
    cv
    cF
    cfv
    cB
    wcel
    vx
    cA
    wral
    wa
    cA
    cB
    cF
    wf
    vx
    cA
    cB
    cF
    elixp.1
    elixp
    vx
    cA
    cB
    cF
    ffnfv
    bitr4i
end
