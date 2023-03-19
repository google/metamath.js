include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "cxp.mm"
include "wf1o.mm"
include "wtru.mm"
include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "wa.mm"
include "copab.mm"
include "wbr.mm"
include "crab.mm"
include "cmpt.mm"
include "cvv.mm"
include "a1i.mm"
include "wi.mm"
include "wal.mm"
include "cab.mm"
include "simpr.mm"
include "elmapi.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "elelpwi.mm"
include "syl2anc.mm"
include "ex.mm"
include "alrimiv.mm"
include "wss.mm"
include "abss.mm"
include "ssex.mm"
include "sylbir.mm"
include "syl.mm"
include "opabex3d.mm"
include "adantl.mm"
include "mptex.mm"
include "wceq.mm"
include "wb.mm"
include "imdistanda.mm"
include "ssopab2dv.mm"
include "df-xp.mm"
include "3sstr4d.mm"
include "selpw.mm"
include "sylibr.mm"
include "feqmptd.mm"
include "nfv.mm"
include "nfopab1.mm"
include "nfeq2.mm"
include "nfan.mm"
include "df-rab.mm"
include "nfopab2.mm"
include "adantllr.mm"
include "cop.mm"
include "df-br.mm"
include "eleq2.mm"
include "opabid.mm"
include "syl6bb.mm"
include "syl5bb.mm"
include "ad2antlr.mm"
include "cdm.mm"
include "elfvdm.mm"
include "wf.mm"
include "fdm.mm"
include "eleqtrd.mm"
include "pm4.71rd.mm"
include "ad2antrr.mm"
include "bitr4d.mm"
include "biimpar.mm"
include "jca.mm"
include "biimpd.mm"
include "adantld.mm"
include "impbid.mm"
include "abbid.mm"
include "abid2.mm"
include "3eqtr2rd.mm"
include "mpteq2da.mm"
include "eqtrd.mm"
include "ssrab2.mm"
include "elpw2.mm"
include "mpbir.mm"
include "eqid.mm"
include "fmptd.mm"
include "feq1d.mm"
include "mpbird.mm"
include "pwex.mm"
include "elmap.mm"
include "wrel.mm"
include "elpwi.mm"
include "xpss.mm"
include "syl6ss.mm"
include "df-rel.mm"
include "relopab.mm"
include "id.mm"
include "nfmpt1.mm"
include "nfci.mm"
include "nfrab1.mm"
include "nfmpt.mm"
include "nfcv.mm"
include "brelg.mm"
include "sylan.mm"
include "adantlr.mm"
include "simpld.mm"
include "simprd.mm"
include "fveq1d.mm"
include "rabex.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "sylan9eq.mm"
include "eleq2d.mm"
include "rabid.mm"
include "syldan.mm"
include "mpbir2and.mm"
include "simplbda.mm"
include "expl.mm"
include "syl5bbr.mm"
include "syl6bbr.mm"
include "eqrelrd2.mm"
include "syl21anc.mm"
include "impbii.mm"
include "f1od.mm"
include "trud.mm"

theorem fpwrelmap
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cM: class M
  let vr: setvar r
  assume fpwrelmap.1: |- A e. _V
  assume fpwrelmap.2: |- B e. _V
  assume fpwrelmap.3: |- M = ( f e. ( ~P B ^m A ) |-> { <. x , y >. | ( x e. A /\ y e. ( f ` x ) ) } )

  disjoint f x
  disjoint f y
  disjoint A f
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B f
  disjoint B x
  disjoint B y
  disjoint f r
  disjoint r x
  disjoint r y
  disjoint A r
  disjoint B r
  assert |- M : ( ~P B ^m A ) -1-1-onto-> ~P ( A X. B )

  proof
    cB
    cpw
    #
    cA
    cmap
    co
    #
    cA
    cB
    cxp
    #
    cpw
    #
    cM
    wf1o
    wtru
    vf
    vr
    @1
    @3
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    @4
    vf
    cv
    #
    cfv
    #
    wcel
    #
    wa
    #
    vx
    vy
    copab
    #
    vx
    cA
    @4
    @6
    vr
    cv
    #
    wbr
    #
    vy
    cB
    crab
    #
    cmpt
    #
    cM
    cvv
    cvv
    fpwrelmap.3
    @7
    @1
    wcel
    #
    @11
    cvv
    wcel
    wtru
    @16
    @9
    vx
    vy
    cA
    cA
    cvv
    wcel
    @16
    fpwrelmap.1
    a1i
    @16
    @5
    wa
    #
    @9
    @6
    cB
    wcel
    #
    wi
    #
    vy
    wal
    #
    @9
    vy
    cab
    #
    cvv
    wcel
    #
    @17
    @19
    vy
    @17
    @9
    @18
    @17
    @9
    wa
    @9
    @8
    @0
    wcel
    #
    @18
    @17
    @9
    simpr
    @17
    @23
    @9
    @16
    cA
    @0
    @4
    @7
    @7
    @0
    cA
    elmapi
    #
    ffvelrnda
    adantr
    @6
    @8
    cB
    elelpwi
    syl2anc
    #
    ex
    #
    alrimiv
    @20
    @21
    cB
    wss
    @22
    @9
    vy
    cB
    abss
    @21
    cB
    fpwrelmap.2
    ssex
    sylbir
    syl
    opabex3d
    adantl
    @15
    cvv
    wcel
    wtru
    @12
    @3
    wcel
    #
    wa
    vx
    cA
    @14
    fpwrelmap.1
    mptex
    a1i
    @16
    @12
    @11
    wceq
    #
    wa
    #
    @27
    @7
    @15
    wceq
    #
    wa
    #
    wb
    wtru
    @29
    @31
    @29
    @27
    @30
    @29
    @12
    @2
    wss
    #
    @27
    @29
    @11
    @5
    @18
    wa
    #
    vx
    vy
    copab
    #
    @12
    @2
    @16
    @11
    @34
    wss
    @28
    @16
    @10
    @33
    vx
    vy
    @16
    @5
    @9
    @18
    @26
    imdistanda
    ssopab2dv
    adantr
    @16
    @28
    simpr
    @2
    @34
    wceq
    @29
    vx
    vy
    cA
    cB
    df-xp
    a1i
    3sstr4d
    vr
    @2
    selpw
    sylibr
    @29
    @7
    vx
    cA
    @8
    cmpt
    #
    @15
    @16
    @7
    @35
    wceq
    @28
    @16
    vx
    cA
    @0
    @7
    @24
    feqmptd
    adantr
    @29
    vx
    cA
    @8
    @14
    @16
    @28
    vx
    @16
    vx
    nfv
    vx
    @12
    @11
    @10
    vx
    vy
    nfopab1
    #
    nfeq2
    nfan
    @29
    @5
    wa
    #
    @14
    @18
    @13
    wa
    #
    vy
    cab
    #
    @21
    @8
    @14
    @39
    wceq
    @37
    @13
    vy
    cB
    df-rab
    a1i
    @37
    @9
    @38
    vy
    @29
    @5
    vy
    @16
    @28
    vy
    @16
    vy
    nfv
    vy
    @12
    @11
    @10
    vx
    vy
    nfopab2
    #
    nfeq2
    nfan
    @5
    vy
    nfv
    #
    nfan
    @37
    @9
    @38
    @37
    @9
    @38
    @37
    @9
    wa
    @18
    @13
    @16
    @5
    @9
    @18
    @28
    @25
    adantllr
    @37
    @13
    @9
    @37
    @13
    @10
    @9
    @28
    @13
    @10
    wb
    @16
    @5
    @13
    @4
    @6
    cop
    #
    @12
    wcel
    #
    @28
    @10
    @4
    @6
    @12
    df-br
    #
    @28
    @43
    @42
    @11
    wcel
    #
    @10
    @12
    @11
    @42
    eleq2
    @10
    vx
    vy
    opabid
    #
    syl6bb
    syl5bb
    ad2antlr
    @16
    @9
    @10
    wb
    @28
    @5
    @16
    @9
    @5
    @16
    @9
    @5
    @16
    @9
    wa
    @4
    @7
    cdm
    #
    cA
    @9
    @4
    @47
    wcel
    @16
    @6
    @4
    @7
    elfvdm
    adantl
    @16
    @47
    cA
    wceq
    #
    @9
    @16
    cA
    @0
    @7
    wf
    #
    @48
    @24
    cA
    @0
    @7
    fdm
    syl
    adantr
    eleqtrd
    ex
    pm4.71rd
    ad2antrr
    bitr4d
    #
    biimpar
    jca
    ex
    @37
    @13
    @9
    @18
    @37
    @13
    @9
    @50
    biimpd
    adantld
    impbid
    abbid
    @21
    @8
    wceq
    @37
    vy
    @8
    abid2
    a1i
    3eqtr2rd
    mpteq2da
    eqtrd
    jca
    @31
    @16
    @28
    @31
    @49
    @16
    @31
    @49
    cA
    @0
    @15
    wf
    #
    @27
    @51
    @30
    @27
    vx
    cA
    @14
    @0
    @15
    @14
    @0
    wcel
    #
    @27
    @5
    wa
    @52
    @14
    cB
    wss
    @13
    vy
    cB
    ssrab2
    @14
    cB
    fpwrelmap.2
    elpw2
    mpbir
    a1i
    @15
    eqid
    #
    fmptd
    adantr
    @31
    cA
    @0
    @7
    @15
    @27
    @30
    simpr
    #
    feq1d
    mpbird
    @0
    cA
    @7
    cB
    fpwrelmap.2
    pwex
    fpwrelmap.1
    elmap
    sylibr
    @31
    @12
    wrel
    #
    @11
    wrel
    #
    @31
    @28
    @31
    @12
    cvv
    cvv
    cxp
    #
    wss
    @55
    @31
    @12
    @2
    @57
    @27
    @32
    @30
    @12
    @2
    elpwi
    #
    adantr
    cA
    cB
    xpss
    syl6ss
    @12
    df-rel
    sylibr
    @56
    @31
    @10
    vx
    vy
    relopab
    a1i
    @31
    id
    @31
    vx
    vy
    @12
    @11
    @27
    @30
    vx
    @27
    vx
    nfv
    vx
    @7
    @15
    vx
    cA
    @14
    nfmpt1
    nfeq2
    nfan
    @27
    @30
    vy
    @27
    vy
    nfv
    vy
    @7
    @15
    vy
    vx
    cA
    @14
    vy
    vx
    cA
    @41
    nfci
    @13
    vy
    cB
    nfrab1
    nfmpt
    nfeq2
    nfan
    vx
    @12
    nfcv
    vy
    @12
    nfcv
    @36
    @40
    @31
    @43
    @10
    @45
    @43
    @13
    @31
    @10
    @44
    @31
    @13
    @10
    @31
    @13
    @10
    @31
    @13
    wa
    #
    @5
    @9
    @59
    @5
    @18
    @27
    @13
    @33
    @30
    @27
    @32
    @13
    @33
    @58
    @4
    @6
    cA
    cB
    @12
    brelg
    sylan
    adantlr
    #
    simpld
    #
    @59
    @9
    @18
    @13
    @59
    @5
    @18
    @60
    simprd
    @31
    @13
    simpr
    @31
    @13
    @5
    @9
    @38
    wb
    @61
    @31
    @5
    wa
    #
    @9
    @6
    @14
    wcel
    @38
    @62
    @8
    @14
    @6
    @31
    @5
    @8
    @4
    @15
    cfv
    #
    @14
    @31
    @4
    @7
    @15
    @54
    fveq1d
    @5
    @14
    cvv
    wcel
    @63
    @14
    wceq
    @13
    vy
    cB
    fpwrelmap.2
    rabex
    vx
    cA
    @14
    cvv
    @15
    @53
    fvmpt2
    mpan2
    sylan9eq
    eleq2d
    @13
    vy
    cB
    rabid
    syl6bb
    #
    syldan
    mpbir2and
    jca
    ex
    @31
    @5
    @9
    @13
    @62
    @9
    @18
    @13
    @64
    simplbda
    expl
    impbid
    syl5bbr
    @46
    syl6bbr
    eqrelrd2
    syl21anc
    jca
    impbii
    a1i
    f1od
    trud
end
