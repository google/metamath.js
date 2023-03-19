include "cn0.mm"
include "wcel.mm"
include "cprime.mm"
include "cfa.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cle.mm"
include "cv.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq2d.mm"
include "breq2.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "fac0.mm"
include "breq2i.mm"
include "nprmdvds1.mm"
include "pm2.21d.mm"
include "syl5bi.mm"
include "wa.mm"
include "wo.mm"
include "cmul.mm"
include "facp1.mm"
include "adantr.mm"
include "cz.mm"
include "wb.mm"
include "simpr.mm"
include "cn.mm"
include "faccl.mm"
include "nnzd.mm"
include "nn0p1nn.mm"
include "euclemma.mm"
include "syl3anc.mm"
include "bitrd.mm"
include "cr.mm"
include "nn0re.mm"
include "lep1d.mm"
include "prmz.mm"
include "adantl.mm"
include "zred.mm"
include "nnred.mm"
include "letr.mm"
include "mpan2d.mm"
include "imim2d.mm"
include "com23.mm"
include "dvdsle.mm"
include "syl2anc.mm"
include "a1dd.mm"
include "jaod.mm"
include "sylbid.mm"
include "ex.mm"
include "a2d.mm"
include "nn0ind.mm"
include "3imp.mm"

theorem prmfac1
  let cP: class P
  let cN: class N
  let vx: setvar x
  let vk: setvar k


  assert |- ( ( N e. NN0 /\ P e. Prime /\ P || ( ! ` N ) ) -> P <_ N )

  proof
    cN
    cn0
    wcel
    cP
    cprime
    wcel
    #
    cP
    cN
    cfa
    cfv
    #
    cdvds
    wbr
    #
    cP
    cN
    cle
    wbr
    #
    @0
    cP
    vx
    cv
    #
    cfa
    cfv
    #
    cdvds
    wbr
    #
    cP
    @4
    cle
    wbr
    #
    wi
    #
    wi
    @0
    cP
    cc0
    cfa
    cfv
    #
    cdvds
    wbr
    #
    cP
    cc0
    cle
    wbr
    #
    wi
    #
    wi
    @0
    cP
    vk
    cv
    #
    cfa
    cfv
    #
    cdvds
    wbr
    #
    cP
    @13
    cle
    wbr
    #
    wi
    #
    wi
    @0
    cP
    @13
    c1
    caddc
    co
    #
    cfa
    cfv
    #
    cdvds
    wbr
    #
    cP
    @18
    cle
    wbr
    #
    wi
    #
    wi
    @0
    @2
    @3
    wi
    #
    wi
    vx
    vk
    cN
    @4
    cc0
    wceq
    #
    @8
    @12
    @0
    @24
    @6
    @10
    @7
    @11
    @24
    @5
    @9
    cP
    cdvds
    @4
    cc0
    cfa
    fveq2
    breq2d
    @4
    cc0
    cP
    cle
    breq2
    imbi12d
    imbi2d
    @4
    @13
    wceq
    #
    @8
    @17
    @0
    @25
    @6
    @15
    @7
    @16
    @25
    @5
    @14
    cP
    cdvds
    @4
    @13
    cfa
    fveq2
    breq2d
    @4
    @13
    cP
    cle
    breq2
    imbi12d
    imbi2d
    @4
    @18
    wceq
    #
    @8
    @22
    @0
    @26
    @6
    @20
    @7
    @21
    @26
    @5
    @19
    cP
    cdvds
    @4
    @18
    cfa
    fveq2
    breq2d
    @4
    @18
    cP
    cle
    breq2
    imbi12d
    imbi2d
    @4
    cN
    wceq
    #
    @8
    @23
    @0
    @27
    @6
    @2
    @7
    @3
    @27
    @5
    @1
    cP
    cdvds
    @4
    cN
    cfa
    fveq2
    breq2d
    @4
    cN
    cP
    cle
    breq2
    imbi12d
    imbi2d
    @10
    cP
    c1
    cdvds
    wbr
    #
    @0
    @11
    @9
    c1
    cP
    cdvds
    fac0
    breq2i
    @0
    @28
    @11
    cP
    nprmdvds1
    pm2.21d
    syl5bi
    @13
    cn0
    wcel
    #
    @0
    @17
    @22
    @29
    @0
    @17
    @22
    wi
    @29
    @0
    wa
    #
    @20
    @17
    @21
    @30
    @20
    @15
    cP
    @18
    cdvds
    wbr
    #
    wo
    #
    @17
    @21
    wi
    #
    @30
    @20
    cP
    @14
    @18
    cmul
    co
    #
    cdvds
    wbr
    #
    @32
    @30
    @19
    @34
    cP
    cdvds
    @29
    @19
    @34
    wceq
    @0
    @13
    facp1
    adantr
    breq2d
    @30
    @0
    @14
    cz
    wcel
    @18
    cz
    wcel
    @35
    @32
    wb
    @29
    @0
    simpr
    @30
    @14
    @29
    @14
    cn
    wcel
    @0
    @13
    faccl
    adantr
    nnzd
    @30
    @18
    @29
    @18
    cn
    wcel
    #
    @0
    @13
    nn0p1nn
    adantr
    #
    nnzd
    cP
    @14
    @18
    euclemma
    syl3anc
    bitrd
    @30
    @15
    @33
    @31
    @30
    @17
    @15
    @21
    @30
    @16
    @21
    @15
    @30
    @16
    @13
    @18
    cle
    wbr
    #
    @21
    @30
    @13
    @29
    @13
    cr
    wcel
    #
    @0
    @13
    nn0re
    adantr
    #
    lep1d
    @30
    cP
    cr
    wcel
    @39
    @18
    cr
    wcel
    @16
    @38
    wa
    @21
    wi
    @30
    cP
    @0
    cP
    cz
    wcel
    #
    @29
    cP
    prmz
    adantl
    #
    zred
    @40
    @30
    @18
    @37
    nnred
    cP
    @13
    @18
    letr
    syl3anc
    mpan2d
    imim2d
    com23
    @30
    @31
    @21
    @17
    @30
    @41
    @36
    @31
    @21
    wi
    @42
    @37
    cP
    @18
    dvdsle
    syl2anc
    a1dd
    jaod
    sylbid
    com23
    ex
    a2d
    nn0ind
    3imp
end
