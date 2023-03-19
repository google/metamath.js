include "wceq.mm"
include "caltop.mm"
include "eqid.mm"
include "altopeq12.mm"
include "mpan2.mm"

theorem altopeq1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> << A , C >> = << B , C >> )

  proof
    cA
    cB
    wceq
    cC
    cC
    wceq
    cA
    cC
    caltop
    cB
    cC
    caltop
    wceq
    cC
    eqid
    cA
    cB
    cC
    cC
    altopeq12
    mpan2
end
