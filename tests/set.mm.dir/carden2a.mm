include "ccrd.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "cen.mm"
include "wbr.mm"
include "df-ne.mm"
include "wa.mm"
include "cdm.mm"
include "wcel.mm"
include "ndmfv.mm"
include "eqeq1.mm"
include "syl5ibr.mm"
include "con1d.mm"
include "imp.mm"
include "cardid2.mm"
include "syl.mm"
include "wi.mm"
include "nsyl4.mm"
include "ensymd.mm"
include "breq2.mm"
include "entr.mm"
include "ex.mm"
include "syl6bi.mm"
include "syl5.mm"
include "mpd.mm"
include "sylan2b.mm"

theorem carden2a
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( ( card ` A ) = ( card ` B ) /\ ( card ` A ) =/= (/) ) -> A ~~ B )

  proof
    cA
    ccrd
    cfv
    #
    c0
    wne
    @0
    cB
    ccrd
    cfv
    #
    wceq
    #
    @0
    c0
    wceq
    #
    wn
    #
    cA
    cB
    cen
    wbr
    #
    @0
    c0
    df-ne
    @2
    @4
    wa
    #
    @1
    cB
    cen
    wbr
    #
    @5
    @6
    cB
    ccrd
    cdm
    #
    wcel
    #
    @7
    @2
    @4
    @9
    @2
    @9
    @3
    @9
    wn
    @3
    @2
    @1
    c0
    wceq
    cB
    ccrd
    ndmfv
    @0
    @1
    c0
    eqeq1
    syl5ibr
    con1d
    imp
    cB
    cardid2
    syl
    @2
    @4
    @7
    @5
    wi
    #
    @4
    cA
    @0
    cen
    wbr
    #
    @2
    @10
    @4
    @0
    cA
    cA
    @8
    wcel
    @0
    cA
    cen
    wbr
    @3
    cA
    cardid2
    cA
    ccrd
    ndmfv
    nsyl4
    ensymd
    @2
    @11
    cA
    @1
    cen
    wbr
    #
    @10
    @0
    @1
    cA
    cen
    breq2
    @12
    @7
    @5
    cA
    @1
    cB
    entr
    ex
    syl6bi
    syl5
    imp
    mpd
    sylan2b
end
