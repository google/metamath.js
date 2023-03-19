include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "cs1.mm"
include "cid.mm"
include "cfv.mm"
include "c0.mm"
include "ids1.mm"
include "fvprc.mm"
include "s1eqd.mm"
include "syl5eq.mm"

theorem s1prc
  let cA: class A


  assert |- ( -. A e. _V -> <" A "> = <" (/) "> )

  proof
    cA
    cvv
    wcel
    wn
    #
    cA
    cs1
    cA
    cid
    cfv
    #
    cs1
    c0
    cs1
    cA
    ids1
    @0
    @1
    c0
    cA
    cid
    fvprc
    s1eqd
    syl5eq
end
