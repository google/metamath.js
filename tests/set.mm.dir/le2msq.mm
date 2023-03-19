include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "clt.mm"
include "wn.mm"
include "cmul.mm"
include "co.mm"
include "wb.mm"
include "lt2msq.mm"
include "ancoms.mm"
include "notbid.mm"
include "simpll.mm"
include "simprl.mm"
include "lenltd.mm"
include "remulcld.mm"
include "3bitr4d.mm"

theorem le2msq
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ 0 <_ A ) /\ ( B e. RR /\ 0 <_ B ) ) -> ( A <_ B <-> ( A x. A ) <_ ( B x. B ) ) )

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
    cB
    cA
    clt
    wbr
    #
    wn
    cB
    cB
    cmul
    co
    #
    cA
    cA
    cmul
    co
    #
    clt
    wbr
    #
    wn
    cA
    cB
    cle
    wbr
    @9
    @8
    cle
    wbr
    @6
    @7
    @10
    @5
    @2
    @7
    @10
    wb
    cB
    cA
    lt2msq
    ancoms
    notbid
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
    lenltd
    @6
    @9
    @8
    @6
    cA
    cA
    @11
    @11
    remulcld
    @6
    cB
    cB
    @12
    @12
    remulcld
    lenltd
    3bitr4d
end
