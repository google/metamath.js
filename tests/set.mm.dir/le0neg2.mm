include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "wb.mm"
include "0re.mm"
include "leneg.mm"
include "mpan.mm"
include "neg0.mm"
include "breq2i.mm"
include "syl6bb.mm"

theorem le0neg2
  let cA: class A


  assert |- ( A e. RR -> ( 0 <_ A <-> -u A <_ 0 ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    cA
    cneg
    #
    cc0
    cneg
    #
    cle
    wbr
    #
    @2
    cc0
    cle
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
    leneg
    mpan
    @3
    cc0
    @2
    cle
    neg0
    breq2i
    syl6bb
end
