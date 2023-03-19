include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "wb.mm"
include "0re.mm"
include "ltadd2.mm"
include "mp3an1.mm"
include "wceq.mm"
include "recn.mm"
include "addid1d.mm"
include "adantl.mm"
include "breq1d.mm"
include "bitrd.mm"

theorem ltaddpos
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( 0 < A <-> B < ( B + A ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cc0
    cA
    clt
    wbr
    #
    cB
    cc0
    caddc
    co
    #
    cB
    cA
    caddc
    co
    #
    clt
    wbr
    #
    cB
    @5
    clt
    wbr
    cc0
    cr
    wcel
    @0
    @1
    @3
    @6
    wb
    0re
    cc0
    cA
    cB
    ltadd2
    mp3an1
    @2
    @4
    cB
    @5
    clt
    @1
    @4
    cB
    wceq
    @0
    @1
    cB
    cB
    recn
    addid1d
    adantl
    breq1d
    bitrd
end
