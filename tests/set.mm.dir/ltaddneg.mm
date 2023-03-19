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
include "mp3an2.mm"
include "wceq.mm"
include "recn.mm"
include "addid1d.mm"
include "adantl.mm"
include "breq2d.mm"
include "bitrd.mm"

theorem ltaddneg
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A < 0 <-> ( B + A ) < B ) )

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
    cA
    cc0
    clt
    wbr
    #
    cB
    cA
    caddc
    co
    #
    cB
    cc0
    caddc
    co
    #
    clt
    wbr
    #
    @4
    cB
    clt
    wbr
    @0
    cc0
    cr
    wcel
    @1
    @3
    @6
    wb
    0re
    cA
    cc0
    cB
    ltadd2
    mp3an2
    @2
    @5
    cB
    @4
    clt
    @1
    @5
    cB
    wceq
    @0
    @1
    cB
    cB
    recn
    addid1d
    adantl
    breq2d
    bitrd
end
