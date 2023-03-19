include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "wb.mm"
include "1re.mm"
include "0lt1.mm"
include "ltrec.mm"
include "mpanr12.mm"
include "1div1e1.mm"
include "breq1i.mm"
include "syl6bb.mm"

theorem reclt1
  let cA: class A


  assert |- ( ( A e. RR /\ 0 < A ) -> ( A < 1 <-> 1 < ( 1 / A ) ) )

  proof
    cA
    cr
    wcel
    cc0
    cA
    clt
    wbr
    wa
    #
    cA
    c1
    clt
    wbr
    #
    c1
    c1
    cdiv
    co
    #
    c1
    cA
    cdiv
    co
    #
    clt
    wbr
    #
    c1
    @3
    clt
    wbr
    @0
    c1
    cr
    wcel
    cc0
    c1
    clt
    wbr
    @1
    @4
    wb
    1re
    0lt1
    cA
    c1
    ltrec
    mpanr12
    @2
    c1
    @3
    clt
    1div1e1
    breq1i
    syl6bb
end
