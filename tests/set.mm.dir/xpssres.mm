include "wss.mm"
include "cxp.mm"
include "cres.mm"
include "cin.mm"
include "cvv.mm"
include "df-res.mm"
include "inxp.mm"
include "inv1.mm"
include "xpeq2i.mm"
include "3eqtri.mm"
include "wceq.mm"
include "sseqin2.mm"
include "biimpi.mm"
include "xpeq1d.mm"
include "syl5eq.mm"

theorem xpssres
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( C C_ A -> ( ( A X. B ) |` C ) = ( C X. B ) )

  proof
    cC
    cA
    wss
    #
    cA
    cB
    cxp
    #
    cC
    cres
    #
    cA
    cC
    cin
    #
    cB
    cxp
    #
    cC
    cB
    cxp
    @2
    @1
    cC
    cvv
    cxp
    cin
    @3
    cB
    cvv
    cin
    #
    cxp
    @4
    @1
    cC
    df-res
    cA
    cB
    cC
    cvv
    inxp
    @5
    cB
    @3
    cB
    inv1
    xpeq2i
    3eqtri
    @0
    @3
    cC
    cB
    @0
    @3
    cC
    wceq
    cC
    cA
    sseqin2
    biimpi
    xpeq1d
    syl5eq
end
