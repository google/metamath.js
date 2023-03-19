include "wss.mm"
include "cres.mm"
include "wceq.mm"
include "resabs2.mm"
include "ax-mp.mm"

theorem resabs2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume resabs2i.1: |- B C_ C


  assert |- ( ( A |` B ) |` C ) = ( A |` B )

  proof
    cB
    cC
    wss
    cA
    cB
    cres
    #
    cC
    cres
    @0
    wceq
    resabs2i.1
    cA
    cB
    cC
    resabs2
    ax-mp
end
