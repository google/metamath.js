include "wss.mm"
include "cin.mm"
include "cres.mm"
include "crn.mm"
include "cima.mm"
include "wceq.mm"
include "sseqin2.mm"
include "reseq2.mm"
include "sylbi.mm"
include "rneqd.mm"
include "df-ima.mm"
include "resres.mm"
include "rneqi.mm"
include "eqtri.mm"
include "3eqtr4g.mm"

theorem resima2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( B C_ C -> ( ( A |` C ) " B ) = ( A " B ) )

  proof
    cB
    cC
    wss
    #
    cA
    cC
    cB
    cin
    #
    cres
    #
    crn
    #
    cA
    cB
    cres
    #
    crn
    cA
    cC
    cres
    #
    cB
    cima
    #
    cA
    cB
    cima
    @0
    @2
    @4
    @0
    @1
    cB
    wceq
    @2
    @4
    wceq
    cB
    cC
    sseqin2
    @1
    cB
    cA
    reseq2
    sylbi
    rneqd
    @6
    @5
    cB
    cres
    #
    crn
    @3
    @5
    cB
    df-ima
    @7
    @2
    cA
    cC
    cB
    resres
    rneqi
    eqtri
    cA
    cB
    df-ima
    3eqtr4g
end
