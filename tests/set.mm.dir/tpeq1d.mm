include "wceq.mm"
include "ctp.mm"
include "tpeq1.mm"
include "syl.mm"

theorem tpeq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume tpeq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> { A , C , D } = { B , C , D } )

  proof
    wph
    cA
    cB
    wceq
    cA
    cC
    cD
    ctp
    cB
    cC
    cD
    ctp
    wceq
    tpeq1d.1
    cA
    cB
    cC
    cD
    tpeq1
    syl
end
