include "wss.mm"
include "wn.mm"
include "wpss.mm"
include "wa.mm"
include "dfpss3.mm"
include "mpbi.mm"
include "simpri.mm"

theorem pssnssi
  let cA: class A
  let cB: class B
  assume pssnssi.1: |- A C. B


  assert |- -. B C_ A

  proof
    cA
    cB
    wss
    #
    cB
    cA
    wss
    wn
    #
    cA
    cB
    wpss
    @0
    @1
    wa
    pssnssi.1
    cA
    cB
    dfpss3
    mpbi
    simpri
end
