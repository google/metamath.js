include "wss.mm"
include "cres.mm"
include "rescom.mm"
include "resabs1.mm"
include "syl5eq.mm"

theorem resabs2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( B C_ C -> ( ( A |` B ) |` C ) = ( A |` B ) )

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
    cA
    cC
    cres
    cB
    cres
    @0
    cA
    cB
    cC
    rescom
    cA
    cB
    cC
    resabs1
    syl5eq
end
