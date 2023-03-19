include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "cale.mm"
include "cfv.mm"
include "csdm.mm"
include "wbr.mm"
include "wi.mm"
include "alephordi.mm"
include "adantl.mm"
include "cdom.mm"
include "cen.mm"
include "wn.mm"
include "brsdom.mm"
include "wss.mm"
include "wne.mm"
include "wb.mm"
include "alephon.mm"
include "domtriord.mm"
include "mp2an.mm"
include "con3d.mm"
include "syl5bi.mm"
include "adantr.mm"
include "ontri1.mm"
include "sylibrd.mm"
include "wceq.mm"
include "fveq2.mm"
include "eqeng.mm"
include "mpsyl.mm"
include "necon3bi.mm"
include "a1i.mm"
include "anim12d.mm"
include "onelpss.mm"
include "impbid.mm"

theorem alephord
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ B e. On ) -> ( A e. B <-> ( aleph ` A ) ~< ( aleph ` B ) ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    wa
    #
    cA
    cB
    wcel
    #
    cA
    cale
    cfv
    #
    cB
    cale
    cfv
    #
    csdm
    wbr
    #
    @1
    @3
    @6
    wi
    @0
    cA
    cB
    alephordi
    adantl
    @6
    @4
    @5
    cdom
    wbr
    #
    @4
    @5
    cen
    wbr
    #
    wn
    #
    wa
    #
    @2
    @3
    @4
    @5
    brsdom
    @2
    @10
    cA
    cB
    wss
    #
    cA
    cB
    wne
    #
    wa
    @3
    @2
    @7
    @11
    @9
    @12
    @2
    @7
    cB
    cA
    wcel
    #
    wn
    #
    @11
    @0
    @7
    @14
    wi
    @1
    @7
    @5
    @4
    csdm
    wbr
    #
    wn
    #
    @0
    @14
    @4
    con0
    wcel
    #
    @5
    con0
    wcel
    @7
    @16
    wb
    cA
    alephon
    #
    cB
    alephon
    @4
    @5
    domtriord
    mp2an
    @0
    @13
    @15
    cB
    cA
    alephordi
    con3d
    syl5bi
    adantr
    cA
    cB
    ontri1
    sylibrd
    @9
    @12
    wi
    @2
    @8
    cA
    cB
    @17
    cA
    cB
    wceq
    @4
    @5
    wceq
    @8
    @18
    cA
    cB
    cale
    fveq2
    @4
    @5
    con0
    eqeng
    mpsyl
    necon3bi
    a1i
    anim12d
    cA
    cB
    onelpss
    sylibrd
    syl5bi
    impbid
end
