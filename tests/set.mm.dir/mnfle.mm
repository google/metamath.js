include "cxr.mm"
include "wcel.mm"
include "cmnf.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "nltmnf.mm"
include "wb.mm"
include "mnfxr.mm"
include "xrlenlt.mm"
include "mpan.mm"
include "mpbird.mm"

theorem mnfle
  let cA: class A


  assert |- ( A e. RR* -> -oo <_ A )

  proof
    cA
    cxr
    wcel
    #
    cmnf
    cA
    cle
    wbr
    #
    cA
    cmnf
    clt
    wbr
    wn
    #
    cA
    nltmnf
    cmnf
    cxr
    wcel
    @0
    @1
    @2
    wb
    mnfxr
    cmnf
    cA
    xrlenlt
    mpan
    mpbird
end
