include "wceq.mm"
include "cpr.mm"
include "preq12.mm"
include "syl2anc.mm"

theorem preq12d
  param wph: wff ph
  param cA: class A
  param cB: class B
  param cC: class C
  param cD: class D
  assume preq1d.1: |- ( ph -> A = B )
  assume preq12d.2: |- ( ph -> C = D )


  assert |- ( ph -> { A , C } = { B , D } )

  proof
    wph
    cA
    cB
    wceq
    cC
    cD
    wceq
    cA
    cC
    cpr
    cB
    cD
    cpr
    wceq
    preq1d.1
    preq12d.2
    cA
    cC
    cB
    cD
    preq12
    syl2anc
end
