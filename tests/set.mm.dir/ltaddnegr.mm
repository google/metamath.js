include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "ltaddneg.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "addcom.mm"
include "syl2anr.mm"
include "breq1d.mm"
include "bitrd.mm"

theorem ltaddnegr
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A < 0 <-> ( A + B ) < B ) )

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
    cB
    cA
    caddc
    co
    #
    cB
    clt
    wbr
    cA
    cB
    caddc
    co
    #
    cB
    clt
    wbr
    cA
    cB
    ltaddneg
    @2
    @3
    @4
    cB
    clt
    @1
    cB
    cc
    wcel
    cA
    cc
    wcel
    @3
    @4
    wceq
    @0
    cB
    recn
    cA
    recn
    cB
    cA
    addcom
    syl2anr
    breq1d
    bitrd
end
