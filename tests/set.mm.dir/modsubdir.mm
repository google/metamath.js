include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "w3a.mm"
include "cc0.mm"
include "cmo.mm"
include "co.mm"
include "cmin.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "modcl.mm"
include "3adant2.mm"
include "3adant1.mm"
include "subge0d.mm"
include "wa.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "cz.mm"
include "resubcl.mm"
include "3adant3.mm"
include "simp3.mm"
include "rerpdivcl.mm"
include "flcld.mm"
include "zsubcld.mm"
include "modcyc2.mm"
include "syl3anc.mm"
include "cc.mm"
include "recn.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "rpre.mm"
include "adantl.mm"
include "refldivcl.mm"
include "remulcld.mm"
include "recnd.mm"
include "sub4d.mm"
include "3ad2ant3.mm"
include "subdid.mm"
include "oveq2d.mm"
include "modval.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "adantr.mm"
include "clt.mm"
include "resubcld.mm"
include "simpl3.mm"
include "simpr.mm"
include "modge0.mm"
include "subge02d.mm"
include "mpbid.mm"
include "modlt.mm"
include "lelttrd.mm"
include "modid.mm"
include "syl22anc.mm"
include "eqtrd.mm"
include "stoic3.mm"
include "breqtrd.mm"
include "impbida.mm"
include "bitr3d.mm"

theorem modsubdir
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR+ ) -> ( ( B mod C ) <_ ( A mod C ) <-> ( ( A - B ) mod C ) = ( ( A mod C ) - ( B mod C ) ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cC
    crp
    wcel
    #
    w3a
    #
    cc0
    cA
    cC
    cmo
    co
    #
    cB
    cC
    cmo
    co
    #
    cmin
    co
    #
    cle
    wbr
    #
    @5
    @4
    cle
    wbr
    cA
    cB
    cmin
    co
    #
    cC
    cmo
    co
    #
    @6
    wceq
    #
    @3
    @4
    @5
    @0
    @2
    @4
    cr
    wcel
    @1
    cA
    cC
    modcl
    3adant2
    #
    @1
    @2
    @5
    cr
    wcel
    @0
    cB
    cC
    modcl
    3adant1
    #
    subge0d
    @3
    @7
    @10
    @3
    @7
    wa
    #
    @9
    @6
    cC
    cmo
    co
    #
    @6
    @3
    @9
    @14
    wceq
    @7
    @3
    @8
    cC
    cA
    cC
    cdiv
    co
    #
    cfl
    cfv
    #
    cB
    cC
    cdiv
    co
    #
    cfl
    cfv
    #
    cmin
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cC
    cmo
    co
    #
    @9
    @14
    @3
    @8
    cr
    wcel
    #
    @2
    @19
    cz
    wcel
    @22
    @9
    wceq
    @0
    @1
    @23
    @2
    cA
    cB
    resubcl
    #
    3adant3
    @0
    @1
    @2
    simp3
    @3
    @16
    @18
    @0
    @2
    @16
    cz
    wcel
    @1
    @0
    @2
    wa
    #
    @15
    cA
    cC
    rerpdivcl
    flcld
    3adant2
    @1
    @2
    @18
    cz
    wcel
    @0
    @1
    @2
    wa
    #
    @17
    cB
    cC
    rerpdivcl
    flcld
    3adant1
    zsubcld
    @8
    cC
    @19
    modcyc2
    syl3anc
    @3
    @21
    @6
    cC
    cmo
    @3
    @8
    cC
    @16
    cmul
    co
    #
    cC
    @18
    cmul
    co
    #
    cmin
    co
    #
    cmin
    co
    cA
    @27
    cmin
    co
    #
    cB
    @28
    cmin
    co
    #
    cmin
    co
    @21
    @6
    @3
    cA
    cB
    @27
    @28
    @0
    @1
    cA
    cc
    wcel
    @2
    cA
    recn
    3ad2ant1
    @1
    @0
    cB
    cc
    wcel
    @2
    cB
    recn
    3ad2ant2
    @0
    @2
    @27
    cc
    wcel
    @1
    @25
    @27
    @25
    cC
    @16
    @2
    cC
    cr
    wcel
    #
    @0
    cC
    rpre
    #
    adantl
    cA
    cC
    refldivcl
    #
    remulcld
    recnd
    3adant2
    @1
    @2
    @28
    cc
    wcel
    @0
    @26
    @28
    @26
    cC
    @18
    @2
    @32
    @1
    @33
    adantl
    cB
    cC
    refldivcl
    #
    remulcld
    recnd
    3adant1
    sub4d
    @3
    @20
    @29
    @8
    cmin
    @3
    cC
    @16
    @18
    @3
    cC
    @2
    @0
    @32
    @1
    @33
    3ad2ant3
    #
    recnd
    @0
    @2
    @16
    cc
    wcel
    @1
    @25
    @16
    @34
    recnd
    3adant2
    @1
    @2
    @18
    cc
    wcel
    @0
    @26
    @18
    @35
    recnd
    3adant1
    subdid
    oveq2d
    @3
    @4
    @30
    @5
    @31
    cmin
    @0
    @2
    @4
    @30
    wceq
    @1
    cA
    cC
    modval
    3adant2
    @1
    @2
    @5
    @31
    wceq
    @0
    cB
    cC
    modval
    3adant1
    oveq12d
    3eqtr4d
    oveq1d
    eqtr3d
    adantr
    @13
    @6
    cr
    wcel
    #
    @2
    @7
    @6
    cC
    clt
    wbr
    #
    @14
    @6
    wceq
    @3
    @37
    @7
    @3
    @4
    @5
    @11
    @12
    resubcld
    #
    adantr
    @0
    @1
    @2
    @7
    simpl3
    @3
    @7
    simpr
    @3
    @38
    @7
    @3
    @6
    @4
    cC
    @39
    @11
    @36
    @3
    cc0
    @5
    cle
    wbr
    #
    @6
    @4
    cle
    wbr
    @1
    @2
    @40
    @0
    cB
    cC
    modge0
    3adant1
    @3
    @4
    @5
    @11
    @12
    subge02d
    mpbid
    @0
    @2
    @4
    cC
    clt
    wbr
    @1
    cA
    cC
    modlt
    3adant2
    lelttrd
    adantr
    @6
    cC
    modid
    syl22anc
    eqtrd
    @3
    @10
    wa
    cc0
    @9
    @6
    cle
    @3
    cc0
    @9
    cle
    wbr
    #
    @10
    @0
    @1
    @23
    @2
    @41
    @24
    @8
    cC
    modge0
    stoic3
    adantr
    @3
    @10
    simpr
    breqtrd
    impbida
    bitr3d
end
