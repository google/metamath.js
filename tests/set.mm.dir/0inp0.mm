include "c0.mm"
include "wceq.mm"
include "csn.mm"
include "wne.mm"
include "0nep0.mm"
include "neeq1.mm"
include "mpbiri.mm"
include "neneqd.mm"

theorem 0inp0
  let cA: class A


  assert |- ( A = (/) -> -. A = { (/) } )

  proof
    cA
    c0
    wceq
    #
    cA
    c0
    csn
    #
    @0
    cA
    @1
    wne
    c0
    @1
    wne
    0nep0
    cA
    c0
    @1
    neeq1
    mpbiri
    neneqd
end
