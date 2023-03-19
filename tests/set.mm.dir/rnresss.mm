include "cres.mm"
include "wss.mm"
include "crn.mm"
include "resss.mm"
include "rnss.mm"
include "ax-mp.mm"

theorem rnresss
  let cA: class A
  let cB: class B


  assert |- ran ( A |` B ) C_ ran A

  proof
    cA
    cB
    cres
    #
    cA
    wss
    @0
    crn
    cA
    crn
    wss
    cA
    cB
    resss
    @0
    cA
    rnss
    ax-mp
end
