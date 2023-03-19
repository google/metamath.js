include "wceq.mm"
include "co.mm"
include "oveq12.mm"
include "mp2an.mm"

theorem oveq12i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  assume oveq1i.1: |- A = B
  assume oveq12i.2: |- C = D


  assert |- ( A F C ) = ( B F D )

  proof
    cA
    cB
    wceq
    cC
    cD
    wceq
    cA
    cC
    cF
    co
    cB
    cD
    cF
    co
    wceq
    oveq1i.1
    oveq12i.2
    cA
    cB
    cC
    cD
    cF
    oveq12
    mp2an
end
