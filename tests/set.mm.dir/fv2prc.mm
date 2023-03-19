include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "cfv.mm"
include "c0.mm"
include "fvprc.mm"
include "fveq1d.mm"
include "0fv.mm"
include "syl6eq.mm"

theorem fv2prc
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( -. A e. _V -> ( ( F ` A ) ` B ) = (/) )

  proof
    cA
    cvv
    wcel
    wn
    #
    cB
    cA
    cF
    cfv
    #
    cfv
    cB
    c0
    cfv
    c0
    @0
    cB
    @1
    c0
    cA
    cF
    fvprc
    fveq1d
    cB
    0fv
    syl6eq
end
