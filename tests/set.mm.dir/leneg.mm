include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cneg.mm"
include "wb.mm"
include "0re.mm"
include "lesub2.mm"
include "mp3an3.mm"
include "df-neg.mm"
include "breq12i.mm"
include "syl6bbr.mm"

theorem leneg
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A <_ B <-> -u B <_ -u A ) )

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
    cle
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
    cle
    wbr
    #
    cB
    cneg
    #
    cA
    cneg
    #
    cle
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
    lesub2
    mp3an3
    @6
    @3
    @7
    @4
    cle
    cB
    df-neg
    cA
    df-neg
    breq12i
    syl6bbr
end
