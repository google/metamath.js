include "wceq.mm"
include "cpr.mm"
include "preq2.mm"
include "syl.mm"

theorem preq2d
  param wph: wff ph
  param cA: class A
  param cB: class B
  param cC: class C
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
