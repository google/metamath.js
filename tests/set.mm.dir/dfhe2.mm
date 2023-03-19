include "whe.mm"
include "cima.mm"
include "wss.mm"
include "cres.mm"
include "cxp.mm"
include "df-he.mm"
include "rp-imass.mm"
include "bitri.mm"

theorem dfhe2
  let cA: class A
  let cR: class R


  assert |- ( R hereditary A <-> ( R |` A ) C_ ( A X. A ) )

  proof
    cA
    cR
    whe
    cR
    cA
    cima
    cA
    wss
    cR
    cA
    cres
    cA
    cA
    cxp
    wss
    cA
    cR
    df-he
    cA
    cA
    cR
    rp-imass
    bitri
end
