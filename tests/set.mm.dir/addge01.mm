include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "wb.mm"
include "0re.mm"
include "leadd2.mm"
include "mp3an1.mm"
include "ancoms.mm"
include "wceq.mm"
include "recn.mm"
include "addid1d.mm"
include "adantr.mm"
include "breq1d.mm"
include "bitrd.mm"

theorem addge01
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( 0 <_ B <-> A <_ ( A + B ) ) )

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
    #
    cA
    cc0
    caddc
    co
    #
    cA
    cB
    caddc
    co
    #
    cle
    wbr
    #
    cA
    @5
    cle
    wbr
    @1
    @0
    @3
    @6
    wb
    #
    cc0
    cr
    wcel
    @1
    @0
    @7
    0re
    cc0
    cB
    cA
    leadd2
    mp3an1
    ancoms
    @2
    @4
    cA
    @5
    cle
    @0
    @4
    cA
    wceq
    @1
    @0
    cA
    cA
    recn
    addid1d
    adantr
    breq1d
    bitrd
end
