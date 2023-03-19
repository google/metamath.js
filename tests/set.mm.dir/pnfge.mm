include "cxr.mm"
include "wcel.mm"
include "cpnf.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "pnfnlt.mm"
include "wb.mm"
include "pnfxr.mm"
include "xrlenlt.mm"
include "mpan2.mm"
include "mpbird.mm"

theorem pnfge
  let cA: class A


  assert |- ( A e. RR* -> A <_ +oo )

  proof
    cA
    cxr
    wcel
    #
    cA
    cpnf
    cle
    wbr
    #
    cpnf
    cA
    clt
    wbr
    wn
    #
    cA
    pnfnlt
    @0
    cpnf
    cxr
    wcel
    @1
    @2
    wb
    pnfxr
    cA
    cpnf
    xrlenlt
    mpan2
    mpbird
end
