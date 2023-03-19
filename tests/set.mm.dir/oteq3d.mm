include "wceq.mm"
include "cotp.mm"
include "oteq3.mm"
include "syl.mm"

theorem oteq3d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume oteq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> <. C , D , A >. = <. C , D , B >. )

  proof
    wph
    cA
    cB
    wceq
    cC
    cD
    cA
    cotp
    cC
    cD
    cB
    cotp
    wceq
    oteq1d.1
    cA
    cB
    cC
    cD
    oteq3
    syl
end
