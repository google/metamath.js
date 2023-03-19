include "wfun.mm"
include "cfn.mm"
include "wcel.mm"
include "cdm.mm"
include "wss.mm"
include "w3a.mm"
include "chash.mm"
include "cfv.mm"
include "cdif.mm"
include "caddc.mm"
include "co.mm"
include "cres.mm"
include "wceq.mm"
include "simp1.mm"
include "wb.mm"
include "hashfun.mm"
include "3ad2ant2.mm"
include "mpbid.mm"
include "cmin.mm"
include "wa.mm"
include "dmfi.mm"
include "anim1i.mm"
include "3adant1.mm"
include "hashssdif.mm"
include "syl.mm"
include "oveq2d.mm"
include "cc.mm"
include "wi.mm"
include "ssfi.mm"
include "ex.mm"
include "hashcl.mm"
include "nn0cnd.mm"
include "syl6.mm"
include "imp.mm"
include "cn0.mm"
include "adantr.mm"
include "jca.mm"
include "pncan3.mm"
include "eqtr2d.mm"
include "hashres.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "3eqtrd.mm"

theorem hashreshashfun
  let cA: class A
  let cB: class B


  assert |- ( ( Fun A /\ A e. Fin /\ B C_ dom A ) -> ( # ` A ) = ( ( # ` ( A |` B ) ) + ( # ` ( dom A \ B ) ) ) )

  proof
    cA
    wfun
    #
    cA
    cfn
    wcel
    #
    cB
    cA
    cdm
    #
    wss
    #
    w3a
    #
    cA
    chash
    cfv
    #
    @2
    chash
    cfv
    #
    cB
    chash
    cfv
    #
    @2
    cB
    cdif
    chash
    cfv
    #
    caddc
    co
    #
    cA
    cB
    cres
    chash
    cfv
    #
    @8
    caddc
    co
    @4
    @0
    @5
    @6
    wceq
    #
    @0
    @1
    @3
    simp1
    @1
    @0
    @0
    @11
    wb
    @3
    cA
    hashfun
    3ad2ant2
    mpbid
    @4
    @9
    @7
    @6
    @7
    cmin
    co
    #
    caddc
    co
    #
    @6
    @4
    @8
    @12
    @7
    caddc
    @4
    @2
    cfn
    wcel
    #
    @3
    wa
    #
    @8
    @12
    wceq
    @1
    @3
    @15
    @0
    @1
    @14
    @3
    cA
    dmfi
    #
    anim1i
    3adant1
    @2
    cB
    hashssdif
    syl
    oveq2d
    @4
    @7
    cc
    wcel
    #
    @6
    cc
    wcel
    #
    wa
    #
    @13
    @6
    wceq
    @1
    @3
    @19
    @0
    @1
    @3
    wa
    @17
    @18
    @1
    @3
    @17
    @1
    @14
    @3
    @17
    wi
    @16
    @14
    @3
    cB
    cfn
    wcel
    #
    @17
    @14
    @3
    @20
    @2
    cB
    ssfi
    ex
    @20
    @7
    cB
    hashcl
    nn0cnd
    syl6
    syl
    imp
    @1
    @18
    @3
    @1
    @6
    @1
    @14
    @6
    cn0
    wcel
    @16
    @2
    hashcl
    syl
    nn0cnd
    adantr
    jca
    3adant1
    @7
    @6
    pncan3
    syl
    eqtr2d
    @4
    @7
    @10
    @8
    caddc
    @4
    @10
    @7
    cA
    cB
    hashres
    eqcomd
    oveq1d
    3eqtrd
end
