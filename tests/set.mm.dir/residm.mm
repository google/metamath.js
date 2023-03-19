include "wss.mm"
include "cres.mm"
include "wceq.mm"
include "ssid.mm"
include "resabs2.mm"
include "ax-mp.mm"

theorem residm
  let cA: class A
  let cB: class B


  assert |- ( ( A |` B ) |` B ) = ( A |` B )

  proof
    cB
    cB
    wss
    cA
    cB
    cres
    #
    cB
    cres
    @0
    wceq
    cB
    ssid
    cA
    cB
    cB
    resabs2
    ax-mp
end
