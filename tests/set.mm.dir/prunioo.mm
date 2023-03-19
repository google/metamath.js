include "cxr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cioo.mm"
include "co.mm"
include "cpr.mm"
include "cun.mm"
include "cicc.mm"
include "wceq.mm"
include "simp3.mm"
include "clt.mm"
include "wo.mm"
include "wb.mm"
include "xrleloe.mm"
include "3adant3.mm"
include "wa.mm"
include "cico.mm"
include "csn.mm"
include "df-pr.mm"
include "uneq2i.mm"
include "unass.mm"
include "eqtr4i.mm"
include "uncom.mm"
include "snunioo.mm"
include "syl5eq.mm"
include "uneq1d.mm"
include "3expa.mm"
include "3adantl3.mm"
include "snunico.mm"
include "adantr.mm"
include "eqtrd.mm"
include "ex.mm"
include "iccid.mm"
include "3ad2ant1.mm"
include "eqcomd.mm"
include "c0.mm"
include "un0.mm"
include "eqtri.mm"
include "iooid.mm"
include "oveq2.mm"
include "syl5eqr.mm"
include "dfsn2.mm"
include "preq2.mm"
include "uneq12d.mm"
include "eqeq12d.mm"
include "syl5ibcom.mm"
include "jaod.mm"
include "sylbid.mm"
include "mpd.mm"

theorem prunioo
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( ( A e. RR* /\ B e. RR* /\ A <_ B ) -> ( ( A (,) B ) u. { A , B } ) = ( A [,] B ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    w3a
    #
    @2
    cA
    cB
    cioo
    co
    #
    cA
    cB
    cpr
    #
    cun
    #
    cA
    cB
    cicc
    co
    #
    wceq
    #
    @0
    @1
    @2
    simp3
    @3
    @2
    cA
    cB
    clt
    wbr
    #
    cA
    cB
    wceq
    #
    wo
    #
    @8
    @0
    @1
    @2
    @11
    wb
    @2
    cA
    cB
    xrleloe
    3adant3
    @3
    @9
    @8
    @10
    @3
    @9
    @8
    @3
    @9
    wa
    @6
    cA
    cB
    cico
    co
    #
    cB
    csn
    #
    cun
    #
    @7
    @0
    @1
    @9
    @6
    @14
    wceq
    #
    @2
    @0
    @1
    @9
    @15
    @0
    @1
    @9
    w3a
    #
    @6
    @4
    cA
    csn
    #
    cun
    #
    @13
    cun
    #
    @14
    @6
    @4
    @17
    @13
    cun
    #
    cun
    @19
    @5
    @20
    @4
    cA
    cB
    df-pr
    uneq2i
    @4
    @17
    @13
    unass
    eqtr4i
    @16
    @18
    @12
    @13
    @16
    @18
    @17
    @4
    cun
    @12
    @4
    @17
    uncom
    cA
    cB
    snunioo
    syl5eq
    uneq1d
    syl5eq
    3expa
    3adantl3
    @3
    @14
    @7
    wceq
    @9
    cA
    cB
    snunico
    adantr
    eqtrd
    ex
    @3
    @17
    cA
    cA
    cicc
    co
    #
    wceq
    @10
    @8
    @3
    @21
    @17
    @0
    @1
    @21
    @17
    wceq
    @2
    cA
    iccid
    3ad2ant1
    eqcomd
    @10
    @17
    @6
    @21
    @7
    @10
    @17
    c0
    @17
    cun
    #
    @6
    @22
    @17
    c0
    cun
    @17
    c0
    @17
    uncom
    @17
    un0
    eqtri
    @10
    c0
    @4
    @17
    @5
    @10
    c0
    cA
    cA
    cioo
    co
    @4
    cA
    iooid
    cA
    cB
    cA
    cioo
    oveq2
    syl5eqr
    @10
    @17
    cA
    cA
    cpr
    @5
    cA
    dfsn2
    cA
    cB
    cA
    preq2
    syl5eq
    uneq12d
    syl5eqr
    cA
    cB
    cA
    cicc
    oveq2
    eqeq12d
    syl5ibcom
    jaod
    sylbid
    mpd
end
