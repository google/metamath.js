include "cr.mm"
include "wcel.mm"
include "cz.mm"
include "crp.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cmo.mm"
include "wceq.mm"
include "w3a.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "wa.mm"
include "zre.mm"
include "rpre.mm"
include "remulcl.mm"
include "syl2an.mm"
include "readdcl.mm"
include "sylan2.mm"
include "3impb.mm"
include "simp3.mm"
include "modval.mm"
include "syl2anc.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "recn.mm"
include "3ad2ant1.mm"
include "recnd.mm"
include "3adant1.mm"
include "rpcnne0.mm"
include "3ad2ant3.mm"
include "divdir.mm"
include "syl3anc.mm"
include "zcn.mm"
include "divcan4.mm"
include "3expb.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "rerpdivcl.mm"
include "3adant2.mm"
include "simp2.mm"
include "fladdz.mm"
include "rpcn.mm"
include "reflcl.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "adddid.mm"
include "mulcom.mm"
include "eqcomd.mm"
include "3eqtrd.mm"
include "adantl.mm"
include "mulcld.mm"
include "pnpcan2d.mm"
include "eqtr4d.mm"
include "3com23.mm"

theorem modcyc
  let cA: class A
  let cB: class B
  let cN: class N


  assert |- ( ( A e. RR /\ B e. RR+ /\ N e. ZZ ) -> ( ( A + ( N x. B ) ) mod B ) = ( A mod B ) )

  proof
    cA
    cr
    wcel
    #
    cN
    cz
    wcel
    #
    cB
    crp
    wcel
    #
    cA
    cN
    cB
    cmul
    co
    #
    caddc
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
    wceq
    @0
    @1
    @2
    w3a
    #
    @5
    cA
    cB
    cA
    cB
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    @6
    @7
    @5
    @4
    cB
    @4
    cB
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    @4
    @10
    @3
    caddc
    co
    #
    cmin
    co
    @11
    @7
    @4
    cr
    wcel
    #
    @2
    @5
    @15
    wceq
    @0
    @1
    @2
    @17
    @1
    @2
    wa
    #
    @0
    @3
    cr
    wcel
    #
    @17
    @1
    cN
    cr
    wcel
    cB
    cr
    wcel
    @19
    @2
    cN
    zre
    cB
    rpre
    cN
    cB
    remulcl
    syl2an
    #
    cA
    @3
    readdcl
    sylan2
    3impb
    @0
    @1
    @2
    simp3
    @4
    cB
    modval
    syl2anc
    @7
    @14
    @16
    @4
    cmin
    @7
    @14
    cB
    @9
    cN
    caddc
    co
    #
    cmul
    co
    @10
    cB
    cN
    cmul
    co
    #
    caddc
    co
    @16
    @7
    @13
    @21
    cB
    cmul
    @7
    @13
    @8
    cN
    caddc
    co
    #
    cfl
    cfv
    #
    @21
    @7
    @12
    @23
    cfl
    @7
    @12
    @8
    @3
    cB
    cdiv
    co
    #
    caddc
    co
    #
    @23
    @7
    cA
    cc
    wcel
    #
    @3
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    wa
    #
    @12
    @26
    wceq
    @0
    @1
    @27
    @2
    cA
    recn
    3ad2ant1
    #
    @1
    @2
    @28
    @0
    @18
    @3
    @20
    recnd
    3adant1
    #
    @2
    @0
    @31
    @1
    cB
    rpcnne0
    #
    3ad2ant3
    cA
    @3
    cB
    divdir
    syl3anc
    @7
    @25
    cN
    @8
    caddc
    @1
    @2
    @25
    cN
    wceq
    #
    @0
    @1
    cN
    cc
    wcel
    #
    @31
    @35
    @2
    cN
    zcn
    #
    @34
    @36
    @29
    @30
    @35
    cN
    cB
    divcan4
    3expb
    syl2an
    3adant1
    oveq2d
    eqtrd
    fveq2d
    @7
    @8
    cr
    wcel
    #
    @1
    @24
    @21
    wceq
    @0
    @2
    @38
    @1
    cA
    cB
    rerpdivcl
    #
    3adant2
    @0
    @1
    @2
    simp2
    @8
    cN
    fladdz
    syl2anc
    eqtrd
    oveq2d
    @7
    cB
    @9
    cN
    @2
    @0
    @29
    @1
    cB
    rpcn
    #
    3ad2ant3
    @0
    @2
    @9
    cc
    wcel
    #
    @1
    @0
    @2
    wa
    #
    @38
    @41
    @39
    @38
    @9
    @8
    reflcl
    recnd
    syl
    #
    3adant2
    @1
    @0
    @36
    @2
    @37
    3ad2ant2
    adddid
    @7
    @22
    @3
    @10
    caddc
    @7
    @3
    @22
    @1
    @2
    @3
    @22
    wceq
    #
    @0
    @1
    @36
    @29
    @44
    @2
    @37
    @40
    cN
    cB
    mulcom
    syl2an
    3adant1
    eqcomd
    oveq2d
    3eqtrd
    oveq2d
    @7
    cA
    @10
    @3
    @32
    @0
    @2
    @10
    cc
    wcel
    @1
    @42
    cB
    @9
    @2
    @29
    @0
    @40
    adantl
    @43
    mulcld
    3adant2
    @33
    pnpcan2d
    3eqtrd
    @0
    @2
    @6
    @11
    wceq
    @1
    cA
    cB
    modval
    3adant2
    eqtr4d
    3com23
end
