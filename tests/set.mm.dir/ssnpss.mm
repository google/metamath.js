include "wpss.mm"
include "wss.mm"
include "wn.mm"
include "dfpss3.mm"
include "simprbi.mm"
include "con2i.mm"

theorem ssnpss
  let cA: class A
  let cB: class B


  assert |- ( A C_ B -> -. B C. A )

  proof
    cB
    cA
    wpss
    #
    cA
    cB
    wss
    #
    @0
    cB
    cA
    wss
    @1
    wn
    cB
    cA
    dfpss3
    simprbi
    con2i
end
