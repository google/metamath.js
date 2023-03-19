include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "addge01.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "addcom.mm"
include "syl2an.mm"
include "breq2d.mm"
include "bitrd.mm"

theorem addge02
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( 0 <_ B <-> A <_ ( B + A ) ) )

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
    cB
    cle
    wbr
    cA
    cA
    cB
    caddc
    co
    #
    cle
    wbr
    cA
    cB
    cA
    caddc
    co
    #
    cle
    wbr
    cA
    cB
    addge01
    @2
    @3
    @4
    cA
    cle
    @0
    cA
    cc
    wcel
    cB
    cc
    wcel
    @3
    @4
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
    bitrd
end
