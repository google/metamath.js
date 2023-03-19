include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "clt.mm"
include "c1.mm"
include "cmin.mm"
include "cmo.mm"
include "wceq.mm"
include "rpre.mm"
include "ax-1rid.mm"
include "syl.mm"
include "adantl.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "adantr.mm"
include "cz.mm"
include "w3a.mm"
include "simpl.mm"
include "simpr.mm"
include "1zzd.mm"
include "3jca.mm"
include "modcyc2.mm"
include "cc0.mm"
include "resubcl.mm"
include "sylan2.mm"
include "jca.mm"
include "wb.mm"
include "subge0.mm"
include "bicomd.mm"
include "caddc.mm"
include "rpcn.mm"
include "2timesd.mm"
include "breq2d.mm"
include "ltsubaddd.mm"
include "bitr4d.mm"
include "anbi12d.mm"
include "biimpa.mm"
include "modid.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"

theorem 2submod
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ B e. RR+ ) /\ ( B <_ A /\ A < ( 2 x. B ) ) ) -> ( A mod B ) = ( A - B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    crp
    wcel
    #
    wa
    #
    cB
    cA
    cle
    wbr
    #
    cA
    c2
    cB
    cmul
    co
    #
    clt
    wbr
    #
    wa
    #
    wa
    #
    cA
    cB
    c1
    cmul
    co
    #
    cmin
    co
    #
    cB
    cmo
    co
    #
    cA
    cB
    cmin
    co
    #
    cB
    cmo
    co
    #
    cA
    cB
    cmo
    co
    #
    @11
    @2
    @10
    @12
    wceq
    @6
    @2
    @9
    @11
    cB
    cmo
    @2
    @8
    cB
    cA
    cmin
    @1
    @8
    cB
    wceq
    #
    @0
    @1
    cB
    cr
    wcel
    #
    @14
    cB
    rpre
    #
    cB
    ax-1rid
    syl
    adantl
    oveq2d
    oveq1d
    adantr
    @7
    @0
    @1
    c1
    cz
    wcel
    #
    w3a
    #
    @10
    @13
    wceq
    @2
    @18
    @6
    @2
    @0
    @1
    @17
    @0
    @1
    simpl
    #
    @0
    @1
    simpr
    #
    @2
    1zzd
    3jca
    adantr
    cA
    cB
    c1
    modcyc2
    syl
    @7
    @11
    cr
    wcel
    #
    @1
    wa
    #
    cc0
    @11
    cle
    wbr
    #
    @11
    cB
    clt
    wbr
    #
    wa
    #
    @12
    @11
    wceq
    @2
    @22
    @6
    @2
    @21
    @1
    @1
    @0
    @15
    @21
    @16
    cA
    cB
    resubcl
    sylan2
    @20
    jca
    adantr
    @2
    @6
    @25
    @2
    @3
    @23
    @5
    @24
    @2
    @23
    @3
    @1
    @0
    @15
    @23
    @3
    wb
    @16
    cA
    cB
    subge0
    sylan2
    bicomd
    @2
    @5
    cA
    cB
    cB
    caddc
    co
    #
    clt
    wbr
    @24
    @2
    @4
    @26
    cA
    clt
    @1
    @4
    @26
    wceq
    @0
    @1
    cB
    cB
    rpcn
    2timesd
    adantl
    breq2d
    @2
    cA
    cB
    cB
    @19
    @1
    @15
    @0
    @16
    adantl
    #
    @27
    ltsubaddd
    bitr4d
    anbi12d
    biimpa
    @11
    cB
    modid
    syl2anc
    3eqtr3d
end
