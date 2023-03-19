include "wf.mm"
include "wrel.mm"
include "frel.mm"
include "syl.mm"

theorem freld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  assume freld.1: |- ( ph -> F : A --> B )


  assert |- ( ph -> Rel F )

  proof
    wph
    cA
    cB
    cF
    wf
    cF
    wrel
    freld.1
    cA
    cB
    cF
    frel
    syl
end
