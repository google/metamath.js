include "cxr.mm"
include "wcel.mm"
include "cmnf.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "wceq.mm"
include "wb.mm"
include "mnfxr.mm"
include "xrlenlt.mm"
include "mpan2.mm"
include "ngtmnft.mm"
include "bitr4d.mm"

theorem xlemnf
  let cA: class A


  assert |- ( A e. RR* -> ( A <_ -oo <-> A = -oo ) )

  proof
    cA
    cxr
    wcel
    #
    cA
    cmnf
    cle
    wbr
    #
    cmnf
    cA
    clt
    wbr
    wn
    #
    cA
    cmnf
    wceq
    @0
    cmnf
    cxr
    wcel
    @1
    @2
    wb
    mnfxr
    cA
    cmnf
    xrlenlt
    mpan2
    cA
    ngtmnft
    bitr4d
end
