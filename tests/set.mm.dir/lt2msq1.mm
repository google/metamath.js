include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "clt.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "simp1l.mm"
include "remulcld.mm"
include "simp2.mm"
include "simp1.mm"
include "simp3.mm"
include "ltled.mm"
include "lemul1a.mm"
include "syl31anc.mm"
include "wb.mm"
include "0red.mm"
include "simp1r.mm"
include "lelttrd.mm"
include "ltmul2.mm"
include "syl112anc.mm"
include "mpbid.mm"

theorem lt2msq1
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ 0 <_ A ) /\ B e. RR /\ A < B ) -> ( A x. A ) < ( B x. B ) )

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
    cA
    cB
    clt
    wbr
    #
    w3a
    #
    cA
    cA
    cmul
    co
    #
    cB
    cA
    cmul
    co
    #
    cB
    cB
    cmul
    co
    #
    @5
    cA
    cA
    @0
    @1
    @3
    @4
    simp1l
    #
    @9
    remulcld
    @5
    cB
    cA
    @2
    @3
    @4
    simp2
    #
    @9
    remulcld
    @5
    cB
    cB
    @10
    @10
    remulcld
    @5
    @0
    @3
    @2
    cA
    cB
    cle
    wbr
    @6
    @7
    cle
    wbr
    @9
    @10
    @2
    @3
    @4
    simp1
    @5
    cA
    cB
    @9
    @10
    @2
    @3
    @4
    simp3
    #
    ltled
    cA
    cB
    cA
    lemul1a
    syl31anc
    @5
    @4
    @7
    @8
    clt
    wbr
    #
    @11
    @5
    @0
    @3
    @3
    cc0
    cB
    clt
    wbr
    @4
    @12
    wb
    @9
    @10
    @10
    @5
    cc0
    cA
    cB
    @5
    0red
    @9
    @10
    @0
    @1
    @3
    @4
    simp1r
    @11
    lelttrd
    cA
    cB
    cB
    ltmul2
    syl112anc
    mpbid
    lelttrd
end
