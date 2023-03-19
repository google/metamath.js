include "wceq.mm"
include "cint.mm"
include "inteq.mm"
include "syl.mm"

theorem inteqd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume inteqd.1: |- ( ph -> A = B )


  assert |- ( ph -> |^| A = |^| B )

  proof
    wph
    cA
    cB
    wceq
    cA
    cint
    cB
    cint
    wceq
    inteqd.1
    cA
    cB
    inteq
    syl
end
