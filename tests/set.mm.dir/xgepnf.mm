include "cxr.mm"
include "wcel.mm"
include "cpnf.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "wceq.mm"
include "wb.mm"
include "pnfxr.mm"
include "xrlenlt.mm"
include "mpan.mm"
include "nltpnft.mm"
include "bitr4d.mm"

theorem xgepnf
  let cA: class A


  assert |- ( A e. RR* -> ( +oo <_ A <-> A = +oo ) )

  proof
    cA
    cxr
    wcel
    #
    cpnf
    cA
    cle
    wbr
    #
    cA
    cpnf
    clt
    wbr
    wn
    #
    cA
    cpnf
    wceq
    cpnf
    cxr
    wcel
    @0
    @1
    @2
    wb
    pnfxr
    cpnf
    cA
    xrlenlt
    mpan
    cA
    nltpnft
    bitr4d
end
