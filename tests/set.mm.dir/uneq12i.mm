include "wceq.mm"
include "cun.mm"
include "uneq12.mm"
include "mp2an.mm"

theorem uneq12i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume uneq1i.1: |- A = B
  assume uneq12i.2: |- C = D


  assert |- ( A u. C ) = ( B u. D )

  proof
    cA
    cB
    wceq
    cC
    cD
    wceq
    cA
    cC
    cun
    cB
    cD
    cun
    wceq
    uneq1i.1
    uneq12i.2
    cA
    cB
    cC
    cD
    uneq12
    mp2an
end
