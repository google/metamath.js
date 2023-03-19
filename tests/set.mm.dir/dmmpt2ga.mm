include "wcel.mm"
include "wral.mm"
include "cxp.mm"
include "wfn.mm"
include "cdm.mm"
include "wceq.mm"
include "fnmpt2.mm"
include "fndm.mm"
include "syl.mm"

theorem dmmpt2ga
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  assume dmmpt2g.f: |- F = ( x e. A , y e. B |-> C )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint V x
  disjoint V y
  assert |- ( A. x e. A A. y e. B C e. V -> dom F = ( A X. B ) )

  proof
    cC
    cV
    wcel
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
    cV
    dmmpt2g.f
    fnmpt2
    @0
    cF
    fndm
    syl
end
