include "wceq.mm"
include "cmpt.mm"
include "mpteq1.mm"
include "syl.mm"

theorem mpteq1d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume mpteq1d.1: |- ( ph -> A = B )

  disjoint A x
  disjoint B x
  assert |- ( ph -> ( x e. A |-> C ) = ( x e. B |-> C ) )

  proof
    wph
    cA
    cB
    wceq
    vx
    cA
    cC
    cmpt
    vx
    cB
    cC
    cmpt
    wceq
    mpteq1d.1
    vx
    cA
    cB
    cC
    mpteq1
    syl
end
