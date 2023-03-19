include "wceq.mm"
include "wa.mm"
include "csn.mm"
include "caltop.mm"
include "sneq.mm"
include "anim12i.mm"
include "altopthsn.mm"
include "sylibr.mm"

theorem altopeq12
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A = B /\ C = D ) -> << A , C >> = << B , D >> )

  proof
    cA
    cB
    wceq
    #
    cC
    cD
    wceq
    #
    wa
    cA
    csn
    cB
    csn
    wceq
    #
    cC
    csn
    cD
    csn
    wceq
    #
    wa
    cA
    cC
    caltop
    cB
    cD
    caltop
    wceq
    @0
    @2
    @1
    @3
    cA
    cB
    sneq
    cC
    cD
    sneq
    anim12i
    cA
    cC
    cB
    cD
    altopthsn
    sylibr
end
