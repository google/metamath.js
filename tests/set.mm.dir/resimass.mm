include "cres.mm"
include "wss.mm"
include "cima.mm"
include "resss.mm"
include "imass1.mm"
include "ax-mp.mm"

theorem resimass
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A |` B ) " C ) C_ ( A " C )

  proof
    cA
    cB
    cres
    #
    cA
    wss
    @0
    cC
    cima
    cA
    cC
    cima
    wss
    cA
    cB
    resss
    @0
    cA
    cC
    imass1
    ax-mp
end
