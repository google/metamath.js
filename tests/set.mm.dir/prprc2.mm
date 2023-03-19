include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "cpr.mm"
include "csn.mm"
include "prcom.mm"
include "prprc1.mm"
include "syl5eq.mm"

theorem prprc2
  let cA: class A
  let cB: class B


  assert |- ( -. B e. _V -> { A , B } = { A } )

  proof
    cB
    cvv
    wcel
    wn
    cA
    cB
    cpr
    cB
    cA
    cpr
    cA
    csn
    cA
    cB
    prcom
    cB
    cA
    prprc1
    syl5eq
end
