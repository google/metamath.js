include "wss.mm"
include "cres.mm"
include "cin.mm"
include "resres.mm"
include "wceq.mm"
include "sseqin2.mm"
include "reseq2.mm"
include "sylbi.mm"
include "syl5eq.mm"

theorem resabs1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( B C_ C -> ( ( A |` C ) |` B ) = ( A |` B ) )

  proof
    cB
    cC
    wss
    #
    cA
    cC
    cres
    cB
    cres
    cA
    cC
    cB
    cin
    #
    cres
    #
    cA
    cB
    cres
    #
    cA
    cC
    cB
    resres
    @0
    @1
    cB
    wceq
    @2
    @3
    wceq
    cB
    cC
    sseqin2
    @1
    cB
    cA
    reseq2
    sylbi
    syl5eq
end
