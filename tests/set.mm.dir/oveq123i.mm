include "co.mm"
include "oveq12i.mm"
include "oveqi.mm"
include "eqtri.mm"

theorem oveq123i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  assume oveq123i.1: |- A = C
  assume oveq123i.2: |- B = D
  assume oveq123i.3: |- F = G


  assert |- ( A F B ) = ( C G D )

  proof
    cA
    cB
    cF
    co
    cC
    cD
    cF
    co
    cC
    cD
    cG
    co
    cA
    cC
    cB
    cD
    cF
    oveq123i.1
    oveq123i.2
    oveq12i
    cF
    cG
    cC
    cD
    oveq123i.3
    oveqi
    eqtri
end
