include "wceq.mm"
include "cotp.mm"
include "oteq2.mm"
include "syl.mm"

theorem oteq2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume oteq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> <. C , A , D >. = <. C , B , D >. )

  proof
    wph
    cA
    cB
    wceq
    cC
    cA
    cD
    cotp
    cC
    cB
    cD
    cotp
    wceq
    oteq1d.1
    cA
    cB
    cC
    cD
    oteq2
    syl
end
