include "ctp.mm"
include "tpeq1d.mm"
include "tpeq2d.mm"
include "tpeq3d.mm"
include "3eqtrd.mm"

theorem tpeq123d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  assume tpeq1d.1: |- ( ph -> A = B )
  assume tpeq123d.2: |- ( ph -> C = D )
  assume tpeq123d.3: |- ( ph -> E = F )


  assert |- ( ph -> { A , C , E } = { B , D , F } )

  proof
    wph
    cA
    cC
    cE
    ctp
    cB
    cC
    cE
    ctp
    cB
    cD
    cE
    ctp
    cB
    cD
    cF
    ctp
    wph
    cA
    cB
    cC
    cE
    tpeq1d.1
    tpeq1d
    wph
    cC
    cD
    cB
    cE
    tpeq123d.2
    tpeq2d
    wph
    cE
    cF
    cB
    cD
    tpeq123d.3
    tpeq3d
    3eqtrd
end
