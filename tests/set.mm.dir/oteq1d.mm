include "wceq.mm"
include "cotp.mm"
include "oteq1.mm"
include "syl.mm"

theorem oteq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume oteq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> <. A , C , D >. = <. B , C , D >. )

  proof
    wph
    cA
    cB
    wceq
    cA
    cC
    cD
    cotp
    cB
    cC
    cD
    cotp
    wceq
    oteq1d.1
    cA
    cB
    cC
    cD
    oteq1
    syl
end
