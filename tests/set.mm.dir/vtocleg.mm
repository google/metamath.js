include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "elisset.mm"
include "exlimiv.mm"
include "syl.mm"

theorem vtocleg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume vtocleg.1: |- ( x = A -> ph )

  disjoint A x
  disjoint ph x
  assert |- ( A e. V -> ph )

  proof
    cA
    cV
    wcel
    vx
    cv
    cA
    wceq
    #
    vx
    wex
    wph
    vx
    cA
    cV
    elisset
    @0
    wph
    vx
    vtocleg.1
    exlimiv
    syl
end
