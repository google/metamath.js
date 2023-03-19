include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wb.mm"
include "0re.mm"
include "suble.mm"
include "mp3an3.mm"
include "simpl.mm"
include "recnd.mm"
include "subid1d.mm"
include "breq1d.mm"
include "bitrd.mm"

theorem suble0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( ( A - B ) <_ 0 <-> A <_ B ) )

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
    cB
    cmin
    co
    cc0
    cle
    wbr
    #
    cA
    cc0
    cmin
    co
    #
    cB
    cle
    wbr
    #
    cA
    cB
    cle
    wbr
    @0
    @1
    cc0
    cr
    wcel
    @3
    @5
    wb
    0re
    cA
    cB
    cc0
    suble
    mp3an3
    @2
    @4
    cA
    cB
    cle
    @2
    cA
    @2
    cA
    @0
    @1
    simpl
    recnd
    subid1d
    breq1d
    bitrd
end
