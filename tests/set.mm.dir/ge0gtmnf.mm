include "cxr.mm"
include "wcel.mm"
include "cmnf.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "mnflt0.mm"
include "wa.mm"
include "wi.mm"
include "mnfxr.mm"
include "0xr.mm"
include "xrltletr.mm"
include "mp3an12.mm"
include "imp.mm"
include "mpanr1.mm"

theorem ge0gtmnf
  let cA: class A


  assert |- ( ( A e. RR* /\ 0 <_ A ) -> -oo < A )

  proof
    cA
    cxr
    wcel
    #
    cmnf
    cc0
    clt
    wbr
    #
    cc0
    cA
    cle
    wbr
    #
    cmnf
    cA
    clt
    wbr
    #
    mnflt0
    @0
    @1
    @2
    wa
    #
    @3
    cmnf
    cxr
    wcel
    cc0
    cxr
    wcel
    @0
    @4
    @3
    wi
    mnfxr
    0xr
    cmnf
    cc0
    cA
    xrltletr
    mp3an12
    imp
    mpanr1
end
