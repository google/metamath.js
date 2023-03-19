include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cxne.mm"
include "wb.mm"
include "0xr.mm"
include "xleneg.mm"
include "mpan.mm"
include "xneg0.mm"
include "breq2i.mm"
include "syl6bb.mm"

theorem xle0neg2
  let cA: class A


  assert |- ( A e. RR* -> ( 0 <_ A <-> -e A <_ 0 ) )

  proof
    cA
    cxr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    cA
    cxne
    #
    cc0
    cxne
    #
    cle
    wbr
    #
    @2
    cc0
    cle
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
    xleneg
    mpan
    @3
    cc0
    @2
    cle
    xneg0
    breq2i
    syl6bb
end
