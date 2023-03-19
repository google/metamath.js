include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "cle.mm"
include "wbr.mm"
include "cfa.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "cv.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "breq2.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "clt.mm"
include "wn.mm"
include "nngt0.mm"
include "cr.mm"
include "wb.mm"
include "0re.mm"
include "nnre.mm"
include "ltnle.mm"
include "sylancr.mm"
include "mpbid.mm"
include "pm2.21d.mm"
include "wa.mm"
include "cmul.mm"
include "wo.mm"
include "peano2nn0.mm"
include "nn0red.mm"
include "leloe.mm"
include "syl2an.mm"
include "nnnn0.mm"
include "nn0leltp1.mm"
include "sylan.mm"
include "nn0p1nn.mm"
include "nnmulcl.mm"
include "sylan2.mm"
include "expcom.mm"
include "adantl.mm"
include "cc.mm"
include "wne.mm"
include "faccl.mm"
include "nncnd.mm"
include "nn0cnd.mm"
include "nncn.mm"
include "nnne0.mm"
include "jca.mm"
include "adantr.mm"
include "div23.mm"
include "syl3anc.mm"
include "sylibrd.mm"
include "imim2d.mm"
include "com23.mm"
include "sylbird.mm"
include "divcan4d.mm"
include "eqeltrd.mm"
include "oveq2.mm"
include "syl5ibcom.mm"
include "a1dd.mm"
include "jaod.mm"
include "sylbid.mm"
include "ex.mm"
include "com34.mm"
include "com12.mm"
include "imp4d.mm"
include "facp1.mm"
include "exp4d.mm"
include "a2d.mm"
include "nn0ind.mm"
include "3imp.mm"

theorem facdiv
  let cM: class M
  let cN: class N
  let vj: setvar j
  let vk: setvar k


  assert |- ( ( M e. NN0 /\ N e. NN /\ N <_ M ) -> ( ( ! ` M ) / N ) e. NN )

  proof
    cM
    cn0
    wcel
    cN
    cn
    wcel
    #
    cN
    cM
    cle
    wbr
    #
    cM
    cfa
    cfv
    #
    cN
    cdiv
    co
    #
    cn
    wcel
    #
    @0
    cN
    vj
    cv
    #
    cle
    wbr
    #
    @5
    cfa
    cfv
    #
    cN
    cdiv
    co
    #
    cn
    wcel
    #
    wi
    #
    wi
    @0
    cN
    cc0
    cle
    wbr
    #
    cc0
    cfa
    cfv
    #
    cN
    cdiv
    co
    #
    cn
    wcel
    #
    wi
    #
    wi
    @0
    cN
    vk
    cv
    #
    cle
    wbr
    #
    @16
    cfa
    cfv
    #
    cN
    cdiv
    co
    #
    cn
    wcel
    #
    wi
    #
    wi
    @0
    cN
    @16
    c1
    caddc
    co
    #
    cle
    wbr
    #
    @22
    cfa
    cfv
    #
    cN
    cdiv
    co
    #
    cn
    wcel
    #
    wi
    #
    wi
    @0
    @1
    @4
    wi
    #
    wi
    vj
    vk
    cM
    @5
    cc0
    wceq
    #
    @10
    @15
    @0
    @29
    @6
    @11
    @9
    @14
    @5
    cc0
    cN
    cle
    breq2
    @29
    @8
    @13
    cn
    @29
    @7
    @12
    cN
    cdiv
    @5
    cc0
    cfa
    fveq2
    oveq1d
    eleq1d
    imbi12d
    imbi2d
    @5
    @16
    wceq
    #
    @10
    @21
    @0
    @30
    @6
    @17
    @9
    @20
    @5
    @16
    cN
    cle
    breq2
    @30
    @8
    @19
    cn
    @30
    @7
    @18
    cN
    cdiv
    @5
    @16
    cfa
    fveq2
    oveq1d
    eleq1d
    imbi12d
    imbi2d
    @5
    @22
    wceq
    #
    @10
    @27
    @0
    @31
    @6
    @23
    @9
    @26
    @5
    @22
    cN
    cle
    breq2
    @31
    @8
    @25
    cn
    @31
    @7
    @24
    cN
    cdiv
    @5
    @22
    cfa
    fveq2
    oveq1d
    eleq1d
    imbi12d
    imbi2d
    @5
    cM
    wceq
    #
    @10
    @28
    @0
    @32
    @6
    @1
    @9
    @4
    @5
    cM
    cN
    cle
    breq2
    @32
    @8
    @3
    cn
    @32
    @7
    @2
    cN
    cdiv
    @5
    cM
    cfa
    fveq2
    oveq1d
    eleq1d
    imbi12d
    imbi2d
    @0
    @11
    @14
    @0
    cc0
    cN
    clt
    wbr
    #
    @11
    wn
    #
    cN
    nngt0
    @0
    cc0
    cr
    wcel
    cN
    cr
    wcel
    #
    @33
    @34
    wb
    0re
    cN
    nnre
    #
    cc0
    cN
    ltnle
    sylancr
    mpbid
    pm2.21d
    @16
    cn0
    wcel
    #
    @0
    @21
    @27
    @37
    @0
    @21
    @23
    @26
    @37
    @0
    @21
    @23
    wa
    wa
    @18
    @22
    cmul
    co
    #
    cN
    cdiv
    co
    #
    cn
    wcel
    #
    @26
    @37
    @0
    @21
    @23
    @40
    @0
    @37
    @21
    @23
    @40
    wi
    wi
    @0
    @37
    @23
    @21
    @40
    @0
    @37
    @23
    @21
    @40
    wi
    #
    wi
    @0
    @37
    wa
    #
    @23
    cN
    @22
    clt
    wbr
    #
    cN
    @22
    wceq
    #
    wo
    #
    @41
    @0
    @35
    @22
    cr
    wcel
    @23
    @45
    wb
    @37
    @36
    @37
    @22
    @16
    peano2nn0
    #
    nn0red
    cN
    @22
    leloe
    syl2an
    @42
    @43
    @41
    @44
    @42
    @43
    @17
    @41
    @0
    cN
    cn0
    wcel
    @37
    @17
    @43
    wb
    cN
    nnnn0
    cN
    @16
    nn0leltp1
    sylan
    @42
    @21
    @17
    @40
    @42
    @20
    @40
    @17
    @42
    @20
    @19
    @22
    cmul
    co
    #
    cn
    wcel
    #
    @40
    @37
    @20
    @48
    wi
    @0
    @20
    @37
    @48
    @37
    @20
    @22
    cn
    wcel
    @48
    @16
    nn0p1nn
    @19
    @22
    nnmulcl
    sylan2
    expcom
    adantl
    @42
    @39
    @47
    cn
    @42
    @18
    cc
    wcel
    #
    @22
    cc
    wcel
    #
    cN
    cc
    wcel
    #
    cN
    cc0
    wne
    #
    wa
    #
    @39
    @47
    wceq
    @37
    @49
    @0
    @37
    @18
    @16
    faccl
    #
    nncnd
    adantl
    #
    @37
    @50
    @0
    @37
    @22
    @46
    nn0cnd
    adantl
    @0
    @53
    @37
    @0
    @51
    @52
    cN
    nncn
    #
    cN
    nnne0
    #
    jca
    adantr
    @18
    @22
    cN
    div23
    syl3anc
    eleq1d
    sylibrd
    imim2d
    com23
    sylbird
    @42
    @44
    @40
    @21
    @42
    @18
    cN
    cmul
    co
    #
    cN
    cdiv
    co
    #
    cn
    wcel
    @44
    @40
    @42
    @59
    @18
    cn
    @42
    @18
    cN
    @55
    @0
    @51
    @37
    @56
    adantr
    @0
    @52
    @37
    @57
    adantr
    divcan4d
    @37
    @18
    cn
    wcel
    @0
    @54
    adantl
    eqeltrd
    @44
    @59
    @39
    cn
    @44
    @58
    @38
    cN
    cdiv
    cN
    @22
    @18
    cmul
    oveq2
    oveq1d
    eleq1d
    syl5ibcom
    a1dd
    jaod
    sylbid
    ex
    com34
    com12
    imp4d
    @37
    @25
    @39
    cn
    @37
    @24
    @38
    cN
    cdiv
    @16
    facp1
    oveq1d
    eleq1d
    sylibrd
    exp4d
    a2d
    nn0ind
    3imp
end
