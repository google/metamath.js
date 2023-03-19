include "wceq.mm"
include "caltop.mm"
include "eqid.mm"
include "altopeq12.mm"
include "mpan.mm"

theorem altopeq2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> << C , A >> = << C , B >> )

  proof
    cC
    cC
    wceq
    cA
    cB
    wceq
    cC
    cA
    caltop
    cC
    cB
    caltop
    wceq
    cC
    eqid
    cC
    cC
    cA
    cB
    altopeq12
    mpan
end
