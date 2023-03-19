include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cneg.mm"
include "wb.mm"
include "0re.mm"
include "ltneg.mm"
include "mpan.mm"
include "neg0.mm"
include "breq2i.mm"
include "syl6bb.mm"

theorem lt0neg2
  let cA: class A


  assert |- ( A e. RR -> ( 0 < A <-> -u A < 0 ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    cA
    cneg
    #
    cc0
    cneg
    #
    clt
    wbr
    #
    @2
    cc0
    clt
    wbr
    cc0
    cr
    wcel
    @0
    @1
    @4
    wb
    0re
    cc0
    cA
    ltneg
    mpan
    @3
    cc0
    @2
    clt
    neg0
    breq2i
    syl6bb
end
