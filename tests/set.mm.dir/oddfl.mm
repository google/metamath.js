include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cmo.mm"
include "co.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "c1.mm"
include "caddc.mm"
include "cmin.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "zre.mm"
include "1red.mm"
include "resubcld.mm"
include "crp.mm"
include "2rp.mm"
include "a1i.mm"
include "lem1d.mm"
include "lediv1dd.mm"
include "rehalfcld.mm"
include "rpreccld.mm"
include "ltaddrpd.mm"
include "zcn.mm"
include "recnd.mm"
include "2cnd.mm"
include "rpne0d.mm"
include "divsubdird.mm"
include "oveq1d.mm"
include "halfcld.mm"
include "reccld.mm"
include "subadd23d.mm"
include "1mhlfehlf.mm"
include "oveq2i.mm"
include "3eqtrrd.mm"
include "breqtrd.mm"
include "jca.mm"
include "adantr.mm"
include "cr.mm"
include "wb.mm"
include "wn.mm"
include "npcand.mm"
include "simpr.mm"
include "neneqd.mm"
include "mod0.mm"
include "syl2anc.mm"
include "mtbid.mm"
include "eqneltrd.mm"
include "simpl.mm"
include "1zzd.mm"
include "zsubcld.mm"
include "zeo2.mm"
include "syl.mm"
include "mpbird.mm"
include "flbi.mm"
include "oveq2d.mm"
include "subcld.mm"
include "divcan2d.mm"

theorem oddfl
  let cK: class K


  assert |- ( ( K e. ZZ /\ ( K mod 2 ) =/= 0 ) -> K = ( ( 2 x. ( |_ ` ( K / 2 ) ) ) + 1 ) )

  proof
    cK
    cz
    wcel
    #
    cK
    c2
    cmo
    co
    #
    cc0
    wne
    #
    wa
    #
    c2
    cK
    c2
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    c1
    caddc
    co
    c2
    cK
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    @7
    c1
    caddc
    co
    #
    cK
    @3
    @6
    @9
    c1
    caddc
    @3
    @5
    @8
    c2
    cmul
    @3
    @5
    @8
    wceq
    #
    @8
    @4
    cle
    wbr
    #
    @4
    @8
    c1
    caddc
    co
    #
    clt
    wbr
    #
    wa
    #
    @0
    @16
    @2
    @0
    @13
    @15
    @0
    @7
    cK
    c2
    @0
    cK
    c1
    cK
    zre
    #
    @0
    1red
    #
    resubcld
    @17
    c2
    crp
    wcel
    #
    @0
    2rp
    a1i
    #
    @0
    cK
    @17
    lem1d
    lediv1dd
    @0
    @4
    @4
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    @14
    clt
    @0
    @4
    @21
    @0
    cK
    @17
    rehalfcld
    @0
    c2
    @20
    rpreccld
    ltaddrpd
    @0
    @14
    @4
    @21
    cmin
    co
    #
    c1
    caddc
    co
    @4
    c1
    @21
    cmin
    co
    #
    caddc
    co
    #
    @22
    @0
    @8
    @23
    c1
    caddc
    @0
    cK
    c1
    c2
    cK
    zcn
    #
    @0
    c1
    @18
    recnd
    #
    @0
    2cnd
    #
    @0
    c2
    @20
    rpne0d
    #
    divsubdird
    oveq1d
    @0
    @4
    @21
    c1
    @0
    cK
    @26
    halfcld
    @0
    c2
    @28
    @29
    reccld
    @27
    subadd23d
    @25
    @22
    wceq
    @0
    @24
    @21
    @4
    caddc
    1mhlfehlf
    oveq2i
    a1i
    3eqtrrd
    breqtrd
    jca
    adantr
    @3
    @4
    cr
    wcel
    @8
    cz
    wcel
    #
    @12
    @16
    wb
    @3
    cK
    @0
    cK
    cr
    wcel
    #
    @2
    @17
    adantr
    rehalfcld
    @3
    @30
    @11
    c2
    cdiv
    co
    #
    cz
    wcel
    wn
    #
    @3
    @32
    @4
    cz
    @0
    @32
    @4
    wceq
    @2
    @0
    @11
    cK
    c2
    cdiv
    @0
    cK
    c1
    @26
    @27
    npcand
    #
    oveq1d
    adantr
    @3
    @1
    cc0
    wceq
    #
    @4
    cz
    wcel
    #
    @3
    @1
    cc0
    @0
    @2
    simpr
    neneqd
    @0
    @35
    @36
    wb
    #
    @2
    @0
    @31
    @19
    @37
    @17
    @20
    cK
    c2
    mod0
    syl2anc
    adantr
    mtbid
    eqneltrd
    @3
    @7
    cz
    wcel
    @30
    @33
    wb
    @3
    cK
    c1
    @0
    @2
    simpl
    @3
    1zzd
    zsubcld
    @7
    zeo2
    syl
    mpbird
    @4
    @8
    flbi
    syl2anc
    mpbird
    oveq2d
    oveq1d
    @0
    @10
    @11
    wceq
    @2
    @0
    @9
    @7
    c1
    caddc
    @0
    @7
    c2
    @0
    cK
    c1
    @26
    @27
    subcld
    @28
    @29
    divcan2d
    oveq1d
    adantr
    @0
    @11
    cK
    wceq
    @2
    @34
    adantr
    3eqtrrd
end
