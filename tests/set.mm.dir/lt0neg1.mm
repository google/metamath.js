include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cneg.mm"
include "wb.mm"
include "0re.mm"
include "ltneg.mm"
include "mpan2.mm"
include "neg0.mm"
include "breq1i.mm"
include "syl6bb.mm"

theorem lt0neg1
  let cA: class A


  assert |- ( A e. RR -> ( A < 0 <-> 0 < -u A ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cc0
    clt
    wbr
    #
    cc0
    cneg
    #
    cA
    cneg
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
    cr
    wcel
    @1
    @4
    wb
    0re
    cA
    cc0
    ltneg
    mpan2
    @2
    cc0
    @3
    clt
    neg0
    breq1i
    syl6bb
end
