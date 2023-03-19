include "wceq.mm"
include "ctp.mm"
include "tpeq2.mm"
include "syl.mm"

theorem tpeq2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume tpeq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> { C , A , D } = { C , B , D } )

  proof
    wph
    cA
    cB
    wceq
    cC
    cA
    cD
    ctp
    cC
    cB
    cD
    ctp
    wceq
    tpeq1d.1
    cA
    cB
    cC
    cD
    tpeq2
    syl
end
