include "cvv.mm"
include "wpss.mm"
include "wss.mm"
include "wceq.mm"
include "wn.mm"
include "ssv.mm"
include "dfpss2.mm"
include "mpbiran.mm"

theorem pssv
  let cA: class A


  assert |- ( A C. _V <-> -. A = _V )

  proof
    cA
    cvv
    wpss
    cA
    cvv
    wss
    cA
    cvv
    wceq
    wn
    cA
    ssv
    cA
    cvv
    dfpss2
    mpbiran
end
