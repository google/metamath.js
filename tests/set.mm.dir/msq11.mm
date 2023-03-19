include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "le2msq.mm"
include "wb.mm"
include "ancoms.mm"
include "anbi12d.mm"
include "simpll.mm"
include "simprl.mm"
include "letri3d.mm"
include "remulcld.mm"
include "3bitr4rd.mm"

theorem msq11
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ 0 <_ A ) /\ ( B e. RR /\ 0 <_ B ) ) -> ( ( A x. A ) = ( B x. B ) <-> A = B ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    cB
    cr
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    #
    wa
    #
    cA
    cB
    cle
    wbr
    #
    cB
    cA
    cle
    wbr
    #
    wa
    cA
    cA
    cmul
    co
    #
    cB
    cB
    cmul
    co
    #
    cle
    wbr
    #
    @10
    @9
    cle
    wbr
    #
    wa
    cA
    cB
    wceq
    @9
    @10
    wceq
    @6
    @7
    @11
    @8
    @12
    cA
    cB
    le2msq
    @5
    @2
    @8
    @12
    wb
    cB
    cA
    le2msq
    ancoms
    anbi12d
    @6
    cA
    cB
    @0
    @1
    @5
    simpll
    #
    @2
    @3
    @4
    simprl
    #
    letri3d
    @6
    @9
    @10
    @6
    cA
    cA
    @13
    @13
    remulcld
    @6
    cB
    cB
    @14
    @14
    remulcld
    letri3d
    3bitr4rd
end
