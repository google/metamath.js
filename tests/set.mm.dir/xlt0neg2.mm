include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cxne.mm"
include "wb.mm"
include "0xr.mm"
include "xltneg.mm"
include "mpan.mm"
include "xneg0.mm"
include "breq2i.mm"
include "syl6bb.mm"

theorem xlt0neg2
  let cA: class A


  assert |- ( A e. RR* -> ( 0 < A <-> -e A < 0 ) )

  proof
    cA
    cxr
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    cA
    cxne
    #
    cc0
    cxne
    #
    clt
    wbr
    #
    @2
    cc0
    clt
    wbr
    cc0
    cxr
    wcel
    @0
    @1
    @4
    wb
    0xr
    cc0
    cA
    xltneg
    mpan
    @3
    cc0
    @2
    clt
    xneg0
    breq2i
    syl6bb
end
