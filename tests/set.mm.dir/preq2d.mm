include "wceq.mm"
include "cpr.mm"
include "preq2.mm"
include "syl.mm"

theorem preq2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume preq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> { C , A } = { C , B } )

  proof
    wph
    cA
    cB
    wceq
    cC
    cA
    cpr
    cC
    cB
    cpr
    wceq
    preq1d.1
    cA
    cB
    cC
    preq2
    syl
end
