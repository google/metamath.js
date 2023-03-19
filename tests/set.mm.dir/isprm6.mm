include "cprime.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "wo.mm"
include "wi.mm"
include "cz.mm"
include "wral.mm"
include "wa.mm"
include "prmuz2.mm"
include "wb.mm"
include "euclemma.mm"
include "3expb.mm"
include "biimpd.mm"
include "ralrimivva.mm"
include "jca.mm"
include "c1.mm"
include "wceq.mm"
include "cn.mm"
include "simpl.mm"
include "cdiv.mm"
include "eluz2nn.mm"
include "adantr.mm"
include "nnzd.mm"
include "iddvds.mm"
include "syl.mm"
include "cc.mm"
include "nncn.mm"
include "ad2antrl.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0.mm"
include "divcan1d.mm"
include "breqtrrd.mm"
include "simprr.mm"
include "simprl.mm"
include "nndivdvds.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "nnz.mm"
include "oveq1.mm"
include "breq2d.mm"
include "breq2.mm"
include "orbi1d.mm"
include "imbi12d.mm"
include "oveq2.mm"
include "orbi2d.mm"
include "rspc2va.mm"
include "sylan.mm"
include "mpd.mm"
include "cle.mm"
include "dvdsle.mm"
include "div1d.mm"
include "breq1d.mm"
include "sylibrd.mm"
include "cr.mm"
include "clt.mm"
include "nnrp.mm"
include "rpregt0d.mm"
include "crp.mm"
include "1rp.mm"
include "rpregt0.mm"
include "mp1i.mm"
include "lediv2.mm"
include "syl3anc.mm"
include "nnle1eq1.mm"
include "sylibd.mm"
include "cn0.mm"
include "nnnn0.mm"
include "simplrr.mm"
include "simpr.mm"
include "dvdseq.mm"
include "syl22anc.mm"
include "ex.mm"
include "orim12d.mm"
include "imp.mm"
include "syldan.mm"
include "an32s.mm"
include "expr.mm"
include "ralrimiva.mm"
include "isprm2.mm"
include "sylanbrc.mm"
include "impbii.mm"

theorem isprm6
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let vz: setvar z

  disjoint x y
  disjoint P x
  disjoint P y
  disjoint x z
  disjoint y z
  disjoint P z
  assert |- ( P e. Prime <-> ( P e. ( ZZ>= ` 2 ) /\ A. x e. ZZ A. y e. ZZ ( P || ( x x. y ) -> ( P || x \/ P || y ) ) ) )

  proof
    cP
    cprime
    wcel
    #
    cP
    c2
    cuz
    cfv
    wcel
    #
    cP
    vx
    cv
    #
    vy
    cv
    #
    cmul
    co
    #
    cdvds
    wbr
    #
    cP
    @2
    cdvds
    wbr
    #
    cP
    @3
    cdvds
    wbr
    #
    wo
    #
    wi
    #
    vy
    cz
    wral
    vx
    cz
    wral
    #
    wa
    #
    @0
    @1
    @10
    cP
    prmuz2
    @0
    @9
    vx
    vy
    cz
    cz
    @0
    @2
    cz
    wcel
    #
    @3
    cz
    wcel
    #
    wa
    wa
    @5
    @8
    @0
    @12
    @13
    @5
    @8
    wb
    cP
    @2
    @3
    euclemma
    3expb
    biimpd
    ralrimivva
    jca
    @11
    @1
    vz
    cv
    #
    cP
    cdvds
    wbr
    #
    @14
    c1
    wceq
    #
    @14
    cP
    wceq
    #
    wo
    #
    wi
    #
    vz
    cn
    wral
    @0
    @1
    @10
    simpl
    @11
    @19
    vz
    cn
    @11
    @14
    cn
    wcel
    #
    @15
    @18
    @1
    @20
    @15
    wa
    #
    @10
    @18
    @1
    @21
    wa
    #
    @10
    cP
    cP
    @14
    cdiv
    co
    #
    cdvds
    wbr
    #
    cP
    @14
    cdvds
    wbr
    #
    wo
    #
    @18
    @22
    @10
    wa
    cP
    @23
    @14
    cmul
    co
    #
    cdvds
    wbr
    #
    @26
    @22
    @28
    @10
    @22
    cP
    cP
    @27
    cdvds
    @22
    cP
    cz
    wcel
    #
    cP
    cP
    cdvds
    wbr
    @22
    cP
    @1
    cP
    cn
    wcel
    #
    @21
    cP
    eluz2nn
    adantr
    #
    nnzd
    #
    cP
    iddvds
    syl
    @22
    cP
    @14
    @22
    @30
    cP
    cc
    wcel
    @31
    cP
    nncn
    syl
    #
    @20
    @14
    cc
    wcel
    @1
    @15
    @14
    nncn
    ad2antrl
    @20
    @14
    cc0
    wne
    @1
    @15
    @14
    nnne0
    ad2antrl
    divcan1d
    breqtrrd
    adantr
    @22
    @23
    cz
    wcel
    #
    @14
    cz
    wcel
    #
    wa
    @10
    @28
    @26
    wi
    #
    @22
    @34
    @35
    @22
    @23
    @22
    @15
    @23
    cn
    wcel
    #
    @1
    @20
    @15
    simprr
    @22
    @30
    @20
    @15
    @37
    wb
    @31
    @1
    @20
    @15
    simprl
    cP
    @14
    nndivdvds
    syl2anc
    mpbid
    #
    nnzd
    @20
    @35
    @1
    @15
    @14
    nnz
    ad2antrl
    jca
    @9
    @36
    cP
    @23
    @3
    cmul
    co
    #
    cdvds
    wbr
    #
    @24
    @7
    wo
    #
    wi
    vx
    vy
    @23
    @14
    cz
    cz
    @2
    @23
    wceq
    #
    @5
    @40
    @8
    @41
    @42
    @4
    @39
    cP
    cdvds
    @2
    @23
    @3
    cmul
    oveq1
    breq2d
    @42
    @6
    @24
    @7
    @2
    @23
    cP
    cdvds
    breq2
    orbi1d
    imbi12d
    @3
    @14
    wceq
    #
    @40
    @28
    @41
    @26
    @43
    @39
    @27
    cP
    cdvds
    @3
    @14
    @23
    cmul
    oveq2
    breq2d
    @43
    @7
    @25
    @24
    @3
    @14
    cP
    cdvds
    breq2
    orbi2d
    imbi12d
    rspc2va
    sylan
    mpd
    @22
    @26
    @18
    @22
    @24
    @16
    @25
    @17
    @22
    @24
    @14
    c1
    cle
    wbr
    #
    @16
    @22
    @24
    cP
    c1
    cdiv
    co
    #
    @23
    cle
    wbr
    #
    @44
    @22
    @24
    cP
    @23
    cle
    wbr
    #
    @46
    @22
    @29
    @37
    @24
    @47
    wi
    @32
    @38
    cP
    @23
    dvdsle
    syl2anc
    @22
    @45
    cP
    @23
    cle
    @22
    cP
    @33
    div1d
    breq1d
    sylibrd
    @22
    @14
    cr
    wcel
    cc0
    @14
    clt
    wbr
    wa
    #
    c1
    cr
    wcel
    cc0
    c1
    clt
    wbr
    wa
    #
    cP
    cr
    wcel
    cc0
    cP
    clt
    wbr
    wa
    @44
    @46
    wb
    @20
    @48
    @1
    @15
    @20
    @14
    @14
    nnrp
    rpregt0d
    ad2antrl
    c1
    crp
    wcel
    @49
    @22
    1rp
    c1
    rpregt0
    mp1i
    @22
    cP
    @22
    @30
    cP
    crp
    wcel
    @31
    cP
    nnrp
    syl
    rpregt0d
    @14
    c1
    cP
    lediv2
    syl3anc
    sylibrd
    @20
    @44
    @16
    wb
    @1
    @15
    @14
    nnle1eq1
    ad2antrl
    sylibd
    @22
    @25
    @17
    @22
    @25
    wa
    @14
    cn0
    wcel
    #
    cP
    cn0
    wcel
    #
    @15
    @25
    @17
    @22
    @50
    @25
    @20
    @50
    @1
    @15
    @14
    nnnn0
    ad2antrl
    adantr
    @22
    @51
    @25
    @22
    @30
    @51
    @31
    cP
    nnnn0
    syl
    adantr
    @1
    @20
    @15
    @25
    simplrr
    @22
    @25
    simpr
    @14
    cP
    dvdseq
    syl22anc
    ex
    orim12d
    imp
    syldan
    an32s
    expr
    ralrimiva
    vz
    cP
    isprm2
    sylanbrc
    impbii
end
