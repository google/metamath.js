include "co.mm"
include "oveqd.mm"
include "oveq12d.mm"
include "eqtrd.mm"

theorem oveq123d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  assume oveq123d.1: |- ( ph -> F = G )
  assume oveq123d.2: |- ( ph -> A = B )
  assume oveq123d.3: |- ( ph -> C = D )


  assert |- ( ph -> ( A F C ) = ( B G D ) )

  proof
    wph
    cA
    cC
    cF
    co
    cA
    cC
    cG
    co
    cB
    cD
    cG
    co
    wph
    cF
    cG
    cA
    cC
    oveq123d.1
    oveqd
    wph
    cA
    cB
    cC
    cD
    cG
    oveq123d.2
    oveq123d.3
    oveq12d
    eqtrd
end
