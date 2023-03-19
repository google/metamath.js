include "cxrn.mm"
include "wrel.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "xrnss3v.mm"
include "xpss.mm"
include "sstri.mm"
include "df-rel.mm"
include "mpbir.mm"

theorem xrnrel
  let cA: class A
  let cB: class B


  assert |- Rel ( A |X. B )

  proof
    cA
    cB
    cxrn
    #
    wrel
    @0
    cvv
    cvv
    cxp
    #
    wss
    @0
    cvv
    @1
    cxp
    @1
    cA
    cB
    xrnss3v
    cvv
    @1
    xpss
    sstri
    @0
    df-rel
    mpbir
end
