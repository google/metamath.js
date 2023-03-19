include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "modge0.mm"
include "modlt.mm"
include "jca.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "syl5ibcom.mm"
include "modid.mm"
include "ex.mm"
include "impbid.mm"

theorem modid2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR+ ) -> ( ( A mod B ) = A <-> ( 0 <_ A /\ A < B ) ) )

  proof
    cA
    cr
    wcel
    cB
    crp
    wcel
    wa
    #
    cA
    cB
    cmo
    co
    #
    cA
    wceq
    #
    cc0
    cA
    cle
    wbr
    #
    cA
    cB
    clt
    wbr
    #
    wa
    #
    @0
    cc0
    @1
    cle
    wbr
    #
    @1
    cB
    clt
    wbr
    #
    wa
    @2
    @5
    @0
    @6
    @7
    cA
    cB
    modge0
    cA
    cB
    modlt
    jca
    @2
    @6
    @3
    @7
    @4
    @1
    cA
    cc0
    cle
    breq2
    @1
    cA
    cB
    clt
    breq1
    anbi12d
    syl5ibcom
    @0
    @5
    @2
    cA
    cB
    modid
    ex
    impbid
end
