include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cneg.mm"
include "wb.mm"
include "0re.mm"
include "ltsub2.mm"
include "mp3an3.mm"
include "df-neg.mm"
include "breq12i.mm"
include "syl6bbr.mm"

theorem ltneg
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A < B <-> -u B < -u A ) )

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
    cA
    cB
    clt
    wbr
    #
    cc0
    cB
    cmin
    co
    #
    cc0
    cA
    cmin
    co
    #
    clt
    wbr
    #
    cB
    cneg
    #
    cA
    cneg
    #
    clt
    wbr
    @0
    @1
    cc0
    cr
    wcel
    @2
    @5
    wb
    0re
    cA
    cB
    cc0
    ltsub2
    mp3an3
    @6
    @3
    @7
    @4
    clt
    cB
    df-neg
    cA
    df-neg
    breq12i
    syl6bbr
end
