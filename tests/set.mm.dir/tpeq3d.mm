include "wceq.mm"
include "ctp.mm"
include "tpeq3.mm"
include "syl.mm"

theorem tpeq3d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume tpeq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> { C , D , A } = { C , D , B } )

  proof
    wph
    cA
    cB
    wceq
    cC
    cD
    cA
    ctp
    cC
    cD
    cB
    ctp
    wceq
    tpeq1d.1
    cA
    cB
    cC
    cD
    tpeq3
    syl
end
