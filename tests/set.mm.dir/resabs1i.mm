include "wss.mm"
include "cres.mm"
include "wceq.mm"
include "resabs1.mm"
include "ax-mp.mm"

theorem resabs1i
  let cA: class A
  let cB: class B
  let cC: class C
  assume resabs1i.1: |- B C_ C


  assert |- ( ( A |` C ) |` B ) = ( A |` B )

  proof
    cB
    cC
    wss
    cA
    cC
    cres
    cB
    cres
    cA
    cB
    cres
    wceq
    resabs1i.1
    cA
    cB
    cC
    resabs1
    ax-mp
end
