include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "wa.mm"
include "clt.mm"
include "wceq.mm"
include "wo.mm"
include "0red.mm"
include "simpl.mm"
include "leloed.mm"
include "simpr.mm"
include "anbi12d.mm"
include "simpll.mm"
include "simplr.mm"
include "remulcld.mm"
include "mulgt0.mm"
include "an4s.mm"
include "ltled.mm"
include "ex.mm"
include "0re.mm"
include "leid.mm"
include "ax-mp.mm"
include "recnd.mm"
include "mul02d.mm"
include "syl5breqr.mm"
include "oveq1.mm"
include "breq2d.mm"
include "syl5ibcom.mm"
include "adantrd.mm"
include "mul01d.mm"
include "oveq2.mm"
include "adantld.mm"
include "ccased.mm"
include "sylbid.mm"
include "imp.mm"

theorem mulge0
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ 0 <_ A ) /\ ( B e. RR /\ 0 <_ B ) ) -> 0 <_ ( A x. B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    cc0
    cB
    cle
    wbr
    #
    cc0
    cA
    cB
    cmul
    co
    #
    cle
    wbr
    #
    @0
    @1
    wa
    #
    @2
    @3
    wa
    #
    @5
    @6
    @7
    cc0
    cA
    clt
    wbr
    #
    cc0
    cA
    wceq
    #
    wo
    #
    cc0
    cB
    clt
    wbr
    #
    cc0
    cB
    wceq
    #
    wo
    #
    wa
    @5
    @6
    @2
    @10
    @3
    @13
    @6
    cc0
    cA
    @6
    0red
    #
    @0
    @1
    simpl
    #
    leloed
    @6
    cc0
    cB
    @14
    @0
    @1
    simpr
    #
    leloed
    anbi12d
    @6
    @8
    @11
    @9
    @12
    @5
    @6
    @8
    @11
    wa
    #
    @5
    @6
    @17
    wa
    #
    cc0
    @4
    @18
    0red
    @18
    cA
    cB
    @0
    @1
    @17
    simpll
    @0
    @1
    @17
    simplr
    remulcld
    @0
    @8
    @1
    @11
    cc0
    @4
    clt
    wbr
    cA
    cB
    mulgt0
    an4s
    ltled
    ex
    @6
    @9
    @5
    @11
    @6
    cc0
    cc0
    cB
    cmul
    co
    #
    cle
    wbr
    @9
    @5
    @6
    cc0
    cc0
    @19
    cle
    cc0
    cr
    wcel
    cc0
    cc0
    cle
    wbr
    0re
    cc0
    leid
    ax-mp
    #
    @6
    cB
    @6
    cB
    @16
    recnd
    mul02d
    syl5breqr
    @9
    @19
    @4
    cc0
    cle
    cc0
    cA
    cB
    cmul
    oveq1
    breq2d
    syl5ibcom
    adantrd
    @6
    @12
    @5
    @8
    @6
    cc0
    cA
    cc0
    cmul
    co
    #
    cle
    wbr
    @12
    @5
    @6
    cc0
    cc0
    @21
    cle
    @20
    @6
    cA
    @6
    cA
    @15
    recnd
    mul01d
    syl5breqr
    @12
    @21
    @4
    cc0
    cle
    cc0
    cB
    cA
    cmul
    oveq2
    breq2d
    syl5ibcom
    #
    adantld
    @6
    @12
    @5
    @9
    @22
    adantld
    ccased
    sylbid
    imp
    an4s
end
