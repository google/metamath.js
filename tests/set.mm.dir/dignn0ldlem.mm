include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cn.mm"
include "clogb.mm"
include "co.mm"
include "cfl.mm"
include "c1.mm"
include "caddc.mm"
include "w3a.mm"
include "ccxp.mm"
include "clt.mm"
include "wbr.mm"
include "cexp.mm"
include "cr.mm"
include "nnre.mm"
include "3ad2ant2.mm"
include "eluzelre.mm"
include "3ad2ant1.mm"
include "cc0.mm"
include "cle.mm"
include "eluz2nn.mm"
include "nnnn0.mm"
include "nn0ge0d.mm"
include "syl.mm"
include "crp.mm"
include "nnrp.mm"
include "relogbzcl.mm"
include "sylan2.mm"
include "3adant3.mm"
include "recxpcld.mm"
include "3ad2ant3.mm"
include "wa.mm"
include "leidd.mm"
include "adantl.mm"
include "cc.mm"
include "cpr.mm"
include "cdif.mm"
include "csn.mm"
include "wceq.mm"
include "eluz2cnn0n1.mm"
include "wne.mm"
include "nncn.mm"
include "nnne0.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "cxplogb.mm"
include "syl2an.mm"
include "breqtrrd.mm"
include "cz.mm"
include "eluz2.mm"
include "wi.mm"
include "flltp1.mm"
include "zre.mm"
include "adantr.mm"
include "ltletr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "ex.mm"
include "com23.mm"
include "3impia.mm"
include "com12.mm"
include "syl5bi.mm"
include "wb.mm"
include "eluz2gt1.mm"
include "jca.mm"
include "cxplt.mm"
include "syl12anc.mm"
include "mpbid.mm"
include "lelttrd.mm"
include "eluzelcn.mm"
include "eluz2n0.mm"
include "eluzelz.mm"
include "cxpexpz.mm"
include "breq2d.mm"

theorem dignn0ldlem
  let cB: class B
  let cK: class K
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( B e. ( ZZ>= ` 2 ) /\ N e. NN /\ K e. ( ZZ>= ` ( ( |_ ` ( B logb N ) ) + 1 ) ) ) -> N < ( B ^ K ) )

  proof
    cB
    c2
    cuz
    cfv
    wcel
    #
    cN
    cn
    wcel
    #
    cK
    cB
    cN
    clogb
    co
    #
    cfl
    cfv
    c1
    caddc
    co
    #
    cuz
    cfv
    wcel
    #
    w3a
    #
    cN
    cB
    cK
    ccxp
    co
    #
    clt
    wbr
    #
    cN
    cB
    cK
    cexp
    co
    #
    clt
    wbr
    #
    @5
    cN
    cB
    @2
    ccxp
    co
    #
    @6
    @1
    @0
    cN
    cr
    wcel
    @4
    cN
    nnre
    #
    3ad2ant2
    @5
    cB
    @2
    @0
    @1
    cB
    cr
    wcel
    #
    @4
    c2
    cB
    eluzelre
    #
    3ad2ant1
    #
    @0
    @1
    cc0
    cB
    cle
    wbr
    #
    @4
    @0
    cB
    cn
    wcel
    #
    @15
    cB
    eluz2nn
    @16
    cB
    cB
    nnnn0
    nn0ge0d
    syl
    3ad2ant1
    #
    @0
    @1
    @2
    cr
    wcel
    #
    @4
    @1
    @0
    cN
    crp
    wcel
    @18
    cN
    nnrp
    cB
    cN
    relogbzcl
    sylan2
    #
    3adant3
    #
    recxpcld
    @5
    cB
    cK
    @14
    @17
    @4
    @0
    cK
    cr
    wcel
    #
    @1
    @3
    cK
    eluzelre
    3ad2ant3
    #
    recxpcld
    @0
    @1
    cN
    @10
    cle
    wbr
    @4
    @0
    @1
    wa
    #
    cN
    cN
    @10
    cle
    @1
    cN
    cN
    cle
    wbr
    @0
    @1
    cN
    @11
    leidd
    adantl
    @0
    cB
    cc
    cc0
    c1
    cpr
    cdif
    wcel
    cN
    cc
    cc0
    csn
    cdif
    wcel
    #
    @10
    cN
    wceq
    @1
    cB
    eluz2cnn0n1
    @1
    cN
    cc
    wcel
    cN
    cc0
    wne
    @24
    cN
    nncn
    cN
    nnne0
    cN
    cc
    cc0
    eldifsn
    sylanbrc
    cB
    cN
    cxplogb
    syl2an
    breqtrrd
    3adant3
    @5
    @2
    cK
    clt
    wbr
    #
    @10
    @6
    clt
    wbr
    #
    @0
    @1
    @4
    @25
    @4
    @3
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    @3
    cK
    cle
    wbr
    #
    w3a
    #
    @23
    @25
    @3
    cK
    eluz2
    @30
    @23
    @25
    @27
    @28
    @29
    @23
    @25
    wi
    @27
    @28
    wa
    #
    @23
    @29
    @25
    @31
    @23
    @29
    @25
    wi
    @31
    @23
    wa
    #
    @2
    @3
    clt
    wbr
    #
    @29
    @25
    @32
    @18
    @33
    @23
    @18
    @31
    @19
    adantl
    #
    @2
    flltp1
    syl
    @32
    @18
    @3
    cr
    wcel
    #
    @21
    @33
    @29
    wa
    @25
    wi
    @34
    @31
    @35
    @23
    @27
    @35
    @28
    @3
    zre
    adantr
    adantr
    @31
    @21
    @23
    @28
    @21
    @27
    cK
    zre
    adantl
    adantr
    @2
    @3
    cK
    ltletr
    syl3anc
    mpand
    ex
    com23
    3impia
    com12
    syl5bi
    3impia
    @5
    @12
    c1
    cB
    clt
    wbr
    #
    wa
    #
    @18
    @21
    @25
    @26
    wb
    @0
    @1
    @37
    @4
    @0
    @12
    @36
    @13
    cB
    eluz2gt1
    jca
    3ad2ant1
    @20
    @22
    cB
    @2
    cK
    cxplt
    syl12anc
    mpbid
    lelttrd
    @5
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    @28
    @7
    @9
    wb
    @0
    @1
    @38
    @4
    c2
    cB
    eluzelcn
    3ad2ant1
    @0
    @1
    @39
    @4
    cB
    eluz2n0
    3ad2ant1
    @4
    @0
    @28
    @1
    @3
    cK
    eluzelz
    3ad2ant3
    @38
    @39
    @28
    w3a
    @6
    @8
    cN
    clt
    cB
    cK
    cxpexpz
    breq2d
    syl3anc
    mpbid
end
