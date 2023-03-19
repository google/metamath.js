include "c0.mm"
include "wne.mm"
include "cxp.mm"
include "wceq.mm"
include "wb.mm"
include "wa.mm"
include "xp11.mm"
include "eqid.mm"
include "biantrur.mm"
include "syl6bbr.mm"
include "wn.mm"
include "wi.mm"
include "nne.mm"
include "simpr.mm"
include "xpeq2.mm"
include "xp0.mm"
include "syl6eq.mm"
include "eqeq1d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "adantl.mm"
include "df-ne.mm"
include "wo.mm"
include "xpeq0.mm"
include "orel1.mm"
include "syl5bi.mm"
include "sylbi.mm"
include "adantr.mm"
include "sylbid.mm"
include "eqtr3.mm"
include "syl6an.mm"
include "sylan2b.mm"
include "impbid1.mm"
include "pm2.61dan.mm"

theorem xpcan
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( C =/= (/) -> ( ( C X. A ) = ( C X. B ) <-> A = B ) )

  proof
    cC
    c0
    wne
    #
    cA
    c0
    wne
    #
    cC
    cA
    cxp
    #
    cC
    cB
    cxp
    #
    wceq
    #
    cA
    cB
    wceq
    #
    wb
    @0
    @1
    wa
    @4
    cC
    cC
    wceq
    #
    @5
    wa
    @5
    cC
    cA
    cC
    cB
    xp11
    @6
    @5
    cC
    eqid
    biantrur
    syl6bbr
    @0
    @1
    wn
    #
    wa
    @4
    @5
    @7
    @0
    cA
    c0
    wceq
    #
    @4
    @5
    wi
    cA
    c0
    nne
    @0
    @8
    wa
    #
    @8
    @4
    cB
    c0
    wceq
    #
    @5
    @0
    @8
    simpr
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
    @0
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
    cC
    c0
    cxp
    c0
    cA
    c0
    cC
    xpeq2
    cC
    xp0
    syl6eq
    eqeq1d
    c0
    @3
    eqcom
    syl6bb
    adantl
    @0
    @11
    @10
    wi
    #
    @8
    @0
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
    @13
    @10
    wo
    @14
    @10
    cC
    cB
    xpeq0
    @13
    @10
    orel1
    syl5bi
    sylbi
    adantr
    sylbid
    cA
    cB
    c0
    eqtr3
    syl6an
    sylan2b
    cA
    cB
    cC
    xpeq2
    impbid1
    pm2.61dan
end
