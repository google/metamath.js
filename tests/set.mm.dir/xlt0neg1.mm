include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cxne.mm"
include "wb.mm"
include "0xr.mm"
include "xltneg.mm"
include "mpan2.mm"
include "xneg0.mm"
include "breq1i.mm"
include "syl6bb.mm"

theorem xlt0neg1
  let cA: class A


  assert |- ( A e. RR* -> ( A < 0 <-> 0 < -e A ) )

  proof
    cA
    cxr
    wcel
    #
    cA
    cc0
    clt
    wbr
    #
    cc0
    cxne
    #
    cA
    cxne
    #
    clt
    wbr
    #
    cc0
    @3
    clt
    wbr
    @0
    cc0
    cxr
    wcel
    @1
    @4
    wb
    0xr
    cA
    cc0
    xltneg
    mpan2
    @2
    cc0
    @3
    clt
    xneg0
    breq1i
    syl6bb
end
