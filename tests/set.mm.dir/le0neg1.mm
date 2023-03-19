include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "wb.mm"
include "0re.mm"
include "leneg.mm"
include "mpan2.mm"
include "neg0.mm"
include "breq1i.mm"
include "syl6bb.mm"

theorem le0neg1
  let cA: class A


  assert |- ( A e. RR -> ( A <_ 0 <-> 0 <_ -u A ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cc0
    cle
    wbr
    #
    cc0
    cneg
    #
    cA
    cneg
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
    cr
    wcel
    @1
    @4
    wb
    0re
    cA
    cc0
    leneg
    mpan2
    @2
    cc0
    @3
    cle
    neg0
    breq1i
    syl6bb
end
