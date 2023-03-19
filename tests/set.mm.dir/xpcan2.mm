include "c0.mm"
include "wne.mm"
include "cxp.mm"
include "wceq.mm"
include "wb.mm"
include "wa.mm"
include "xp11.mm"
include "eqid.mm"
include "biantru.mm"
include "syl6bbr.mm"
include "wn.mm"
include "nne.mm"
include "simpl.mm"
include "xpeq1.mm"
include "0xp.mm"
include "syl6eq.mm"
include "eqeq1d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "adantr.mm"
include "wi.mm"
include "df-ne.mm"
include "wo.mm"
include "xpeq0.mm"
include "orel2.mm"
include "syl5bi.mm"
include "sylbi.mm"
include "adantl.mm"
include "sylbid.mm"
include "eqtr3.mm"
include "syl6an.mm"
include "impbid1.mm"
include "sylanb.mm"
include "pm2.61ian.mm"

theorem xpcan2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( C =/= (/) -> ( ( A X. C ) = ( B X. C ) <-> A = B ) )

  proof
    cA
    c0
    wne
    #
    cC
    c0
    wne
    #
    cA
    cC
    cxp
    #
    cB
    cC
    cxp
    #
    wceq
    #
    cA
    cB
    wceq
    #
    wb
    #
    @0
    @1
    wa
    @4
    @5
    cC
    cC
    wceq
    #
    wa
    @5
    cA
    cC
    cB
    cC
    xp11
    @7
    @5
    cC
    eqid
    biantru
    syl6bbr
    @0
    wn
    cA
    c0
    wceq
    #
    @1
    @6
    cA
    c0
    nne
    @8
    @1
    wa
    #
    @4
    @5
    @9
    @8
    @4
    cB
    c0
    wceq
    #
    @5
    @8
    @1
    simpl
    @9
    @4
    @3
    c0
    wceq
    #
    @10
    @8
    @4
    @11
    wb
    @1
    @8
    @4
    c0
    @3
    wceq
    @11
    @8
    @2
    c0
    @3
    @8
    @2
    c0
    cC
    cxp
    c0
    cA
    c0
    cC
    xpeq1
    cC
    0xp
    syl6eq
    eqeq1d
    c0
    @3
    eqcom
    syl6bb
    adantr
    @1
    @11
    @10
    wi
    #
    @8
    @1
    cC
    c0
    wceq
    #
    wn
    #
    @12
    cC
    c0
    df-ne
    @11
    @10
    @13
    wo
    @14
    @10
    cB
    cC
    xpeq0
    @13
    @10
    orel2
    syl5bi
    sylbi
    adantl
    sylbid
    cA
    cB
    c0
    eqtr3
    syl6an
    cA
    cB
    cC
    xpeq1
    impbid1
    sylanb
    pm2.61ian
end
