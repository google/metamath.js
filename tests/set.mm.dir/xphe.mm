include "cxp.mm"
include "whe.mm"
include "cima.mm"
include "wss.mm"
include "crn.mm"
include "imassrn.mm"
include "rnxpss.mm"
include "sstri.mm"
include "df-he.mm"
include "mpbir.mm"

theorem xphe
  let cA: class A
  let cB: class B


  assert |- ( A X. B ) hereditary B

  proof
    cB
    cA
    cB
    cxp
    #
    whe
    @0
    cB
    cima
    #
    cB
    wss
    @1
    @0
    crn
    cB
    @0
    cB
    imassrn
    cA
    cB
    rnxpss
    sstri
    cB
    @0
    df-he
    mpbir
end
