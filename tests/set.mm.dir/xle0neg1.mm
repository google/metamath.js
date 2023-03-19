include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cxne.mm"
include "wb.mm"
include "0xr.mm"
include "xleneg.mm"
include "mpan2.mm"
include "xneg0.mm"
include "breq1i.mm"
include "syl6bb.mm"

theorem xle0neg1
  let cA: class A


  assert |- ( A e. RR* -> ( A <_ 0 <-> 0 <_ -e A ) )

  proof
    cA
    cxr
    wcel
    #
    cA
    cc0
    cle
    wbr
    #
    cc0
    cxne
    #
    cA
    cxne
    #
    cle
    wbr
    #
    cc0
    @3
    cle
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
    xleneg
    mpan2
    @2
    cc0
    @3
    cle
    xneg0
    breq1i
    syl6bb
end
