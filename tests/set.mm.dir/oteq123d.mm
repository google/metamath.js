include "cotp.mm"
include "oteq1d.mm"
include "oteq2d.mm"
include "oteq3d.mm"
include "3eqtrd.mm"

theorem oteq123d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  assume oteq1d.1: |- ( ph -> A = B )
  assume oteq123d.2: |- ( ph -> C = D )
  assume oteq123d.3: |- ( ph -> E = F )


  assert |- ( ph -> <. A , C , E >. = <. B , D , F >. )

  proof
    wph
    cA
    cC
    cE
    cotp
    cB
    cC
    cE
    cotp
    cB
    cD
    cE
    cotp
    cB
    cD
    cF
    cotp
    wph
    cA
    cB
    cC
    cE
    oteq1d.1
    oteq1d
    wph
    cC
    cD
    cB
    cE
    oteq123d.2
    oteq2d
    wph
    cE
    cF
    cB
    cD
    oteq123d.3
    oteq3d
    3eqtrd
end
