include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "cpr.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "csn.mm"
include "cun.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wn.mm"
include "simpr.mm"
include "elsni.mm"
include "eqcomd.mm"
include "necon3ai.mm"
include "cfn.mm"
include "snfi.mm"
include "hashunsng.mm"
include "imp.mm"
include "mpanr1.mm"
include "syl2an.mm"
include "hashsng.mm"
include "adantr.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "df-pr.mm"
include "fveq2i.mm"
include "df-2.mm"
include "3eqtr4g.mm"
include "1ne2.mm"
include "a1i.mm"
include "eqnetrd.mm"
include "dfsn2.mm"
include "preq2.mm"
include "syl5req.mm"
include "fveq2d.mm"
include "neeq1d.mm"
include "syl5ibrcom.mm"
include "necon2d.mm"
include "impbida.mm"

theorem hashprg
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( A =/= B <-> ( # ` { A , B } ) = 2 ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    cA
    cB
    wne
    #
    cA
    cB
    cpr
    #
    chash
    cfv
    #
    c2
    wceq
    #
    @2
    @3
    wa
    #
    cA
    csn
    #
    cB
    csn
    cun
    #
    chash
    cfv
    #
    c1
    c1
    caddc
    co
    #
    @5
    c2
    @7
    @10
    @8
    chash
    cfv
    #
    c1
    caddc
    co
    #
    @11
    @2
    @1
    cB
    @8
    wcel
    #
    wn
    #
    @10
    @13
    wceq
    #
    @3
    @0
    @1
    simpr
    @14
    cA
    cB
    @14
    cB
    cA
    cB
    cA
    elsni
    eqcomd
    necon3ai
    @1
    @8
    cfn
    wcel
    #
    @15
    @16
    cA
    snfi
    @1
    @17
    @15
    wa
    @16
    @8
    cB
    cW
    hashunsng
    imp
    mpanr1
    syl2an
    @7
    @12
    c1
    c1
    caddc
    @2
    @12
    c1
    wceq
    #
    @3
    @0
    @18
    @1
    cA
    cV
    hashsng
    adantr
    #
    adantr
    oveq1d
    eqtrd
    @4
    @9
    chash
    cA
    cB
    df-pr
    fveq2i
    df-2
    3eqtr4g
    @2
    @6
    @3
    @2
    cA
    cB
    @5
    c2
    @2
    @5
    c2
    wne
    cA
    cB
    wceq
    #
    @12
    c2
    wne
    @2
    @12
    c1
    c2
    @19
    c1
    c2
    wne
    @2
    1ne2
    a1i
    eqnetrd
    @20
    @5
    @12
    c2
    @20
    @4
    @8
    chash
    @20
    @8
    cA
    cA
    cpr
    @4
    cA
    dfsn2
    cA
    cB
    cA
    preq2
    syl5req
    fveq2d
    neeq1d
    syl5ibrcom
    necon2d
    imp
    impbida
end
