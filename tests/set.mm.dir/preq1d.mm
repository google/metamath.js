include "wceq.mm"
include "cpr.mm"
include "preq1.mm"
include "syl.mm"

theorem preq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume preq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> { A , C } = { B , C } )

  proof
    wph
    cA
    cB
    wceq
    cA
    cC
    cpr
    cB
    cC
    cpr
    wceq
    preq1d.1
    cA
    cB
    cC
    preq1
    syl
end
