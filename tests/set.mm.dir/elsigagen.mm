include "wcel.mm"
include "csigagen.mm"
include "cfv.mm"
include "sssigagen.mm"
include "sselda.mm"

theorem elsigagen
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( ( A e. V /\ B e. A ) -> B e. ( sigaGen ` A ) )

  proof
    cA
    cV
    wcel
    cA
    cA
    csigagen
    cfv
    cB
    cA
    cV
    sssigagen
    sselda
end
