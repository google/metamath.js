include "ctxp.mm"
include "wrel.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "txpss3v.mm"
include "xpss.mm"
include "sstri.mm"
include "df-rel.mm"
include "mpbir.mm"

theorem txprel
  let cA: class A
  let cB: class B


  assert |- Rel ( A (x) B )

  proof
    cA
    cB
    ctxp
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
    txpss3v
    cvv
    @1
    xpss
    sstri
    @0
    df-rel
    mpbir
end
