include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "cpr.mm"
include "csn.mm"
include "c0.mm"
include "prprc1.mm"
include "wceq.mm"
include "snprc.mm"
include "biimpi.mm"
include "sylan9eq.mm"

theorem prprc
  let cA: class A
  let cB: class B


  assert |- ( ( -. A e. _V /\ -. B e. _V ) -> { A , B } = (/) )

  proof
    cA
    cvv
    wcel
    wn
    cB
    cvv
    wcel
    wn
    #
    cA
    cB
    cpr
    cB
    csn
    #
    c0
    cA
    cB
    prprc1
    @0
    @1
    c0
    wceq
    cB
    snprc
    biimpi
    sylan9eq
end
