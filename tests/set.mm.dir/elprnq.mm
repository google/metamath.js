include "cnp.mm"
include "wcel.mm"
include "cnq.mm"
include "prpssnq.mm"
include "pssssd.mm"
include "sselda.mm"

theorem elprnq
  let cA: class A
  let cB: class B


  assert |- ( ( A e. P. /\ B e. A ) -> B e. Q. )

  proof
    cA
    cnp
    wcel
    #
    cA
    cnq
    cB
    @0
    cA
    cnq
    cA
    prpssnq
    pssssd
    sselda
end
