include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "ltaddpos.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "addcom.mm"
include "syl2an.mm"
include "breq2d.mm"
include "bitr4d.mm"

theorem ltaddpos2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( 0 < A <-> B < ( A + B ) ) )

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
    cB
    cB
    cA
    caddc
    co
    #
    clt
    wbr
    cB
    cA
    cB
    caddc
    co
    #
    clt
    wbr
    cA
    cB
    ltaddpos
    @2
    @4
    @3
    cB
    clt
    @0
    cA
    cc
    wcel
    cB
    cc
    wcel
    @4
    @3
    wceq
    @1
    cA
    recn
    cB
    recn
    cA
    cB
    addcom
    syl2an
    breq2d
    bitr4d
end
