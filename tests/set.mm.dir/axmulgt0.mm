include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cltrr.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "clt.mm"
include "ax-pre-mulgt0.mm"
include "wb.mm"
include "0re.mm"
include "ltxrlt.mm"
include "mpan.mm"
include "bi2anan9.mm"
include "remulcl.mm"
include "sylancr.mm"
include "3imtr4d.mm"

theorem axmulgt0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( ( 0 < A /\ 0 < B ) -> 0 < ( A x. B ) ) )

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
    cltrr
    wbr
    #
    cc0
    cB
    cltrr
    wbr
    #
    wa
    cc0
    cA
    cB
    cmul
    co
    #
    cltrr
    wbr
    #
    cc0
    cA
    clt
    wbr
    #
    cc0
    cB
    clt
    wbr
    #
    wa
    cc0
    @5
    clt
    wbr
    #
    cA
    cB
    ax-pre-mulgt0
    @0
    @7
    @3
    @1
    @8
    @4
    cc0
    cr
    wcel
    #
    @0
    @7
    @3
    wb
    0re
    cc0
    cA
    ltxrlt
    mpan
    @10
    @1
    @8
    @4
    wb
    0re
    cc0
    cB
    ltxrlt
    mpan
    bi2anan9
    @2
    @10
    @5
    cr
    wcel
    @9
    @6
    wb
    0re
    cA
    cB
    remulcl
    cc0
    @5
    ltxrlt
    sylancr
    3imtr4d
end
