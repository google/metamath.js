include "cn0.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "wrex.mm"
include "cz.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "simpr.mm"
include "adantr.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "cc.mm"
include "nn0cn.mm"
include "ad2antrr.mm"
include "cr.mm"
include "nn0re.mm"
include "modcl.mm"
include "sylan.mm"
include "recnd.mm"
include "wb.mm"
include "eleq1.mm"
include "adantl.mm"
include "mpbid.mm"
include "zcn.mm"
include "rpcn.mm"
include "mulcld.mm"
include "subadd2d.mm"
include "eqcom.mm"
include "syl6rbbr.mm"
include "wne.mm"
include "subcld.mm"
include "rpcnne0.mm"
include "divmul3.mm"
include "syl3anc.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "eqcoms.mm"
include "moddiffl.mm"
include "eqtrd.mm"
include "eqeq1d.mm"
include "3bitr2d.mm"
include "wi.mm"
include "clt.mm"
include "nn0ge0.mm"
include "jca.mm"
include "rpregt0.mm"
include "divge0.mm"
include "syl2an.mm"
include "rpre.mm"
include "rpne0.mm"
include "redivcld.mm"
include "0z.mm"
include "flge.mm"
include "sylancl.mm"
include "breq2.mm"
include "syl5ibcom.mm"
include "sylbid.mm"
include "imp.mm"
include "elnn0z.mm"
include "sylanbrc.mm"
include "weq.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcedvd.mm"
include "nn0z.mm"
include "modmuladdim.mm"
include "r19.29a.mm"
include "ex.mm"

theorem modmuladdnn0
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cM: class M
  let vi: setvar i

  disjoint A k
  disjoint B k
  disjoint M k
  disjoint A i
  disjoint i k
  disjoint B i
  disjoint M i
  assert |- ( ( A e. NN0 /\ M e. RR+ ) -> ( ( A mod M ) = B -> E. k e. NN0 A = ( ( k x. M ) + B ) ) )

  proof
    cA
    cn0
    wcel
    #
    cM
    crp
    wcel
    #
    wa
    #
    cA
    cM
    cmo
    co
    #
    cB
    wceq
    #
    cA
    vk
    cv
    #
    cM
    cmul
    co
    #
    cB
    caddc
    co
    #
    wceq
    #
    vk
    cn0
    wrex
    #
    @2
    @4
    wa
    #
    cA
    vi
    cv
    #
    cM
    cmul
    co
    #
    cB
    caddc
    co
    #
    wceq
    #
    @9
    vi
    cz
    @10
    @11
    cz
    wcel
    #
    wa
    #
    @14
    wa
    #
    @8
    @14
    vk
    @11
    cn0
    @17
    @15
    cc0
    @11
    cle
    wbr
    #
    @11
    cn0
    wcel
    @16
    @15
    @14
    @10
    @15
    simpr
    adantr
    @16
    @14
    @18
    @16
    @14
    cA
    cM
    cdiv
    co
    #
    cfl
    cfv
    #
    @11
    wceq
    #
    @18
    @16
    @14
    cA
    cB
    cmin
    co
    #
    @12
    wceq
    #
    @22
    cM
    cdiv
    co
    #
    @11
    wceq
    #
    @21
    @16
    @23
    @13
    cA
    wceq
    @14
    @16
    cA
    cB
    @12
    @2
    cA
    cc
    wcel
    #
    @4
    @15
    @0
    @26
    @1
    cA
    nn0cn
    #
    adantr
    ad2antrr
    @10
    cB
    cc
    wcel
    #
    @15
    @10
    @3
    cc
    wcel
    #
    @28
    @2
    @29
    @4
    @2
    @3
    @0
    cA
    cr
    wcel
    #
    @1
    @3
    cr
    wcel
    cA
    nn0re
    #
    cA
    cM
    modcl
    sylan
    recnd
    adantr
    @4
    @29
    @28
    wb
    @2
    @3
    cB
    cc
    eleq1
    adantl
    mpbid
    #
    adantr
    @16
    @11
    cM
    @15
    @11
    cc
    wcel
    #
    @10
    @11
    zcn
    adantl
    #
    @2
    cM
    cc
    wcel
    #
    @4
    @15
    @1
    @35
    @0
    cM
    rpcn
    adantl
    ad2antrr
    mulcld
    subadd2d
    cA
    @13
    eqcom
    syl6rbbr
    @16
    @22
    cc
    wcel
    #
    @33
    @35
    cM
    cc0
    wne
    #
    wa
    #
    @25
    @23
    wb
    @10
    @36
    @15
    @10
    cA
    cB
    @0
    @26
    @1
    @4
    @27
    ad2antrr
    @32
    subcld
    adantr
    @34
    @2
    @38
    @4
    @15
    @1
    @38
    @0
    cM
    rpcnne0
    adantl
    ad2antrr
    @22
    @11
    cM
    divmul3
    syl3anc
    @16
    @24
    @20
    @11
    @16
    @24
    cA
    @3
    cmin
    co
    #
    cM
    cdiv
    co
    #
    @20
    @10
    @24
    @40
    wceq
    #
    @15
    @4
    @41
    @2
    @41
    cB
    @3
    cB
    @3
    wceq
    @22
    @39
    cM
    cdiv
    cB
    @3
    cA
    cmin
    oveq2
    oveq1d
    eqcoms
    adantl
    adantr
    @2
    @40
    @20
    wceq
    #
    @4
    @15
    @0
    @30
    @1
    @42
    @31
    cA
    cM
    moddiffl
    sylan
    ad2antrr
    eqtrd
    eqeq1d
    3bitr2d
    @2
    @21
    @18
    wi
    @4
    @15
    @2
    cc0
    @20
    cle
    wbr
    #
    @21
    @18
    @2
    cc0
    @19
    cle
    wbr
    #
    @43
    @0
    @30
    cc0
    cA
    cle
    wbr
    #
    wa
    cM
    cr
    wcel
    #
    cc0
    cM
    clt
    wbr
    wa
    @44
    @1
    @0
    @30
    @45
    @31
    cA
    nn0ge0
    jca
    cM
    rpregt0
    cA
    cM
    divge0
    syl2an
    @2
    @19
    cr
    wcel
    cc0
    cz
    wcel
    @44
    @43
    wb
    @2
    cA
    cM
    @0
    @30
    @1
    @31
    adantr
    @1
    @46
    @0
    cM
    rpre
    adantl
    @1
    @37
    @0
    cM
    rpne0
    adantl
    redivcld
    0z
    @19
    cc0
    flge
    sylancl
    mpbid
    @20
    @11
    cc0
    cle
    breq2
    syl5ibcom
    ad2antrr
    sylbid
    imp
    @11
    elnn0z
    sylanbrc
    vk
    vi
    weq
    #
    @8
    @14
    wb
    @17
    @47
    @7
    @13
    cA
    @47
    @6
    @12
    cB
    caddc
    @5
    @11
    cM
    cmul
    oveq1
    oveq1d
    eqeq2d
    adantl
    @16
    @14
    simpr
    rspcedvd
    @2
    @4
    @14
    vi
    cz
    wrex
    #
    @0
    cA
    cz
    wcel
    @1
    @4
    @48
    wi
    cA
    nn0z
    cA
    cB
    vi
    cM
    modmuladdim
    sylan
    imp
    r19.29a
    ex
end
