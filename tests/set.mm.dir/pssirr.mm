include "wpss.mm"
include "wss.mm"
include "wn.mm"
include "wa.mm"
include "pm3.24.mm"
include "dfpss3.mm"
include "mtbir.mm"

theorem pssirr
  let cA: class A


  assert |- -. A C. A

  proof
    cA
    cA
    wpss
    cA
    cA
    wss
    #
    @0
    wn
    wa
    @0
    pm3.24
    cA
    cA
    dfpss3
    mtbir
end
