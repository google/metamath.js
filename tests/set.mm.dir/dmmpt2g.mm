include "wcel.mm"
include "wral.mm"
include "cdm.mm"
include "cxp.mm"
include "wceq.mm"
include "cv.mm"
include "wa.mm"
include "simpl.mm"
include "ralrimivva.mm"
include "dmmpt2ga.mm"
include "syl.mm"

theorem dmmpt2g
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
  disjoint C x
  disjoint C y
  assert |- ( C e. V -> dom F = ( A X. B ) )

  proof
    cC
    cV
    wcel
    #
    @0
    vy
    cB
    wral
    vx
    cA
    wral
    cF
    cdm
    cA
    cB
    cxp
    wceq
    @0
    @0
    vx
    vy
    cA
    cB
    @0
    vx
    cv
    cA
    wcel
    vy
    cv
    cB
    wcel
    wa
    simpl
    ralrimivva
    vx
    vy
    cA
    cB
    cC
    cF
    cV
    dmmpt2g.f
    dmmpt2ga
    syl
end
