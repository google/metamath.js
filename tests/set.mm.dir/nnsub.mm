include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "breq2.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "nnnlt1.mm"
include "pm2.21d.mm"
include "rgen.mm"
include "breq1.mm"
include "oveq2.mm"
include "cbvralv.mm"
include "cc.mm"
include "nncn.mm"
include "adantr.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "simpl.mm"
include "eqeltrd.mm"
include "syl5ibrcom.mm"
include "a1dd.mm"
include "rspcv.mm"
include "cr.mm"
include "wb.mm"
include "nnre.mm"
include "1re.mm"
include "ltsubadd.mm"
include "mp3an2.mm"
include "syl2anr.mm"
include "subsub3.mm"
include "mp3an3.mm"
include "syl2an.mm"
include "biimpd.mm"
include "syl9r.mm"
include "wo.mm"
include "nn1m1nn.mm"
include "adantl.mm"
include "mpjaod.mm"
include "ralrimdva.mm"
include "syl5bi.mm"
include "nnind.mm"
include "rspcva.mm"
include "sylan2.mm"
include "cc0.mm"
include "nngt0.mm"
include "posdif.mm"
include "syl5ibr.mm"
include "impbid.mm"

theorem nnsub
  let cA: class A
  let cB: class B
  let vz: setvar z
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. NN /\ B e. NN ) -> ( A < B <-> ( B - A ) e. NN ) )

  proof
    cA
    cn
    wcel
    #
    cB
    cn
    wcel
    #
    wa
    #
    cA
    cB
    clt
    wbr
    #
    cB
    cA
    cmin
    co
    #
    cn
    wcel
    #
    @1
    @0
    vz
    cv
    #
    cB
    clt
    wbr
    #
    cB
    @6
    cmin
    co
    #
    cn
    wcel
    #
    wi
    #
    vz
    cn
    wral
    #
    @3
    @5
    wi
    #
    @6
    vx
    cv
    #
    clt
    wbr
    #
    @13
    @6
    cmin
    co
    #
    cn
    wcel
    #
    wi
    #
    vz
    cn
    wral
    @6
    c1
    clt
    wbr
    #
    c1
    @6
    cmin
    co
    #
    cn
    wcel
    #
    wi
    #
    vz
    cn
    wral
    @6
    vy
    cv
    #
    clt
    wbr
    #
    @22
    @6
    cmin
    co
    #
    cn
    wcel
    #
    wi
    #
    vz
    cn
    wral
    #
    @6
    @22
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @28
    @6
    cmin
    co
    #
    cn
    wcel
    #
    wi
    #
    vz
    cn
    wral
    #
    @11
    vx
    vy
    cB
    @13
    c1
    wceq
    #
    @17
    @21
    vz
    cn
    @34
    @14
    @18
    @16
    @20
    @13
    c1
    @6
    clt
    breq2
    @34
    @15
    @19
    cn
    @13
    c1
    @6
    cmin
    oveq1
    eleq1d
    imbi12d
    ralbidv
    @13
    @22
    wceq
    #
    @17
    @26
    vz
    cn
    @35
    @14
    @23
    @16
    @25
    @13
    @22
    @6
    clt
    breq2
    @35
    @15
    @24
    cn
    @13
    @22
    @6
    cmin
    oveq1
    eleq1d
    imbi12d
    ralbidv
    @13
    @28
    wceq
    #
    @17
    @32
    vz
    cn
    @36
    @14
    @29
    @16
    @31
    @13
    @28
    @6
    clt
    breq2
    @36
    @15
    @30
    cn
    @13
    @28
    @6
    cmin
    oveq1
    eleq1d
    imbi12d
    ralbidv
    @13
    cB
    wceq
    #
    @17
    @10
    vz
    cn
    @37
    @14
    @7
    @16
    @9
    @13
    cB
    @6
    clt
    breq2
    @37
    @15
    @8
    cn
    @13
    cB
    @6
    cmin
    oveq1
    eleq1d
    imbi12d
    ralbidv
    @21
    vz
    cn
    @6
    cn
    wcel
    #
    @18
    @20
    @6
    nnnlt1
    pm2.21d
    rgen
    @27
    @13
    @22
    clt
    wbr
    #
    @22
    @13
    cmin
    co
    #
    cn
    wcel
    #
    wi
    #
    vx
    cn
    wral
    #
    @22
    cn
    wcel
    #
    @33
    @26
    @42
    vz
    vx
    cn
    @6
    @13
    wceq
    #
    @23
    @39
    @25
    @41
    @6
    @13
    @22
    clt
    breq1
    @45
    @24
    @40
    cn
    @6
    @13
    @22
    cmin
    oveq2
    eleq1d
    imbi12d
    cbvralv
    @44
    @43
    @32
    vz
    cn
    @44
    @38
    wa
    #
    @6
    c1
    wceq
    #
    @43
    @32
    wi
    @6
    c1
    cmin
    co
    #
    cn
    wcel
    #
    @46
    @47
    @32
    @43
    @46
    @47
    @31
    @29
    @46
    @31
    @47
    @28
    c1
    cmin
    co
    #
    cn
    wcel
    @46
    @50
    @22
    cn
    @46
    @22
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @50
    @22
    wceq
    @44
    @51
    @38
    @22
    nncn
    #
    adantr
    ax-1cn
    @22
    c1
    pncan
    sylancl
    @44
    @38
    simpl
    eqeltrd
    @47
    @30
    @50
    cn
    @6
    c1
    @28
    cmin
    oveq2
    eleq1d
    syl5ibrcom
    a1dd
    a1dd
    @49
    @43
    @48
    @22
    clt
    wbr
    #
    @22
    @48
    cmin
    co
    #
    cn
    wcel
    #
    wi
    #
    @46
    @32
    @42
    @57
    vx
    @48
    cn
    @13
    @48
    wceq
    #
    @39
    @54
    @41
    @56
    @13
    @48
    @22
    clt
    breq1
    @58
    @40
    @55
    cn
    @13
    @48
    @22
    cmin
    oveq2
    eleq1d
    imbi12d
    rspcv
    @46
    @57
    @32
    @46
    @54
    @29
    @56
    @31
    @38
    @6
    cr
    wcel
    #
    @22
    cr
    wcel
    #
    @54
    @29
    wb
    #
    @44
    @6
    nnre
    @22
    nnre
    @59
    c1
    cr
    wcel
    @60
    @61
    1re
    @6
    c1
    @22
    ltsubadd
    mp3an2
    syl2anr
    @46
    @55
    @30
    cn
    @44
    @51
    @6
    cc
    wcel
    #
    @55
    @30
    wceq
    #
    @38
    @53
    @6
    nncn
    @51
    @62
    @52
    @63
    ax-1cn
    @22
    @6
    c1
    subsub3
    mp3an3
    syl2an
    eleq1d
    imbi12d
    biimpd
    syl9r
    @38
    @47
    @49
    wo
    @44
    @6
    nn1m1nn
    adantl
    mpjaod
    ralrimdva
    syl5bi
    nnind
    @10
    @12
    vz
    cA
    cn
    @6
    cA
    wceq
    #
    @7
    @3
    @9
    @5
    @6
    cA
    cB
    clt
    breq1
    @64
    @8
    @4
    cn
    @6
    cA
    cB
    cmin
    oveq2
    eleq1d
    imbi12d
    rspcva
    sylan2
    @5
    @3
    @2
    cc0
    @4
    clt
    wbr
    #
    @4
    nngt0
    @0
    cA
    cr
    wcel
    cB
    cr
    wcel
    @3
    @65
    wb
    @1
    cA
    nnre
    cB
    nnre
    cA
    cB
    posdif
    syl2an
    syl5ibr
    impbid
end
