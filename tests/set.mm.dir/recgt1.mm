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
include "mpanl12.mm"
include "1div1e1.mm"
include "breq2i.mm"
include "syl6bb.mm"

theorem recgt1
  let cA: class A


  assert |- ( ( A e. RR /\ 0 < A ) -> ( 1 < A <-> ( 1 / A ) < 1 ) )

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
    c1
    cA
    clt
    wbr
    #
    c1
    cA
    cdiv
    co
    #
    c1
    c1
    cdiv
    co
    #
    clt
    wbr
    #
    @2
    c1
    clt
    wbr
    c1
    cr
    wcel
    cc0
    c1
    clt
    wbr
    @0
    @1
    @4
    wb
    1re
    0lt1
    c1
    cA
    ltrec
    mpanl12
    @3
    c1
    @2
    clt
    1div1e1
    breq2i
    syl6bb
end
