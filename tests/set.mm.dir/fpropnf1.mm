include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "wfun.mm"
include "ccnv.mm"
include "wn.mm"
include "cop.mm"
include "cpr.mm"
include "id.mm"
include "3adant3.mm"
include "adantr.mm"
include "jca.mm"
include "3ad2ant3.mm"
include "simpr.mm"
include "3jca.mm"
include "funprg.mm"
include "syl.mm"
include "funeqi.mm"
include "sylibr.mm"
include "wceq.mm"
include "neneq.mm"
include "adantl.mm"
include "wf.mm"
include "fprg.mm"
include "eqcomi.mm"
include "feq1i.mm"
include "sylib.mm"
include "wf1.mm"
include "df-f1.mm"
include "cv.mm"
include "cfv.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "dff13.mm"
include "wb.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "ralprg.mm"
include "eqeq2d.mm"
include "eqeq2.mm"
include "anbi12d.mm"
include "fveq1i.mm"
include "3simpb.mm"
include "anim1i.mm"
include "df-3an.mm"
include "fvpr1g.mm"
include "syl5eq.mm"
include "3simpc.mm"
include "fvpr2g.mm"
include "syl5req.mm"
include "eqtrd.mm"
include "idd.mm"
include "embantd.mm"
include "adantld.mm"
include "adantrd.mm"
include "sylbid.mm"
include "syl5bi.mm"
include "syl5bir.mm"
include "mpand.mm"
include "mtod.mm"

theorem fpropnf1
  let cU: class U
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  assume fpropnf1.f: |- F = { <. X , Z >. , <. Y , Z >. }


  assert |- ( ( ( X e. U /\ Y e. V /\ Z e. W ) /\ X =/= Y ) -> ( Fun F /\ -. Fun `' F ) )

  proof
    cX
    cU
    wcel
    #
    cY
    cV
    wcel
    #
    cZ
    cW
    wcel
    #
    w3a
    #
    cX
    cY
    wne
    #
    wa
    #
    cF
    wfun
    #
    cF
    ccnv
    wfun
    #
    wn
    @5
    cX
    cZ
    cop
    cY
    cZ
    cop
    cpr
    #
    wfun
    #
    @6
    @5
    @0
    @1
    wa
    #
    @2
    @2
    wa
    #
    @4
    w3a
    #
    @9
    @5
    @10
    @11
    @4
    @3
    @10
    @4
    @0
    @1
    @10
    @2
    @10
    id
    3adant3
    adantr
    @3
    @11
    @4
    @2
    @0
    @11
    @1
    @2
    @2
    @2
    @2
    id
    #
    @13
    jca
    3ad2ant3
    adantr
    @3
    @4
    simpr
    3jca
    #
    cX
    cY
    cZ
    cZ
    cU
    cV
    cW
    cW
    funprg
    syl
    cF
    @8
    fpropnf1.f
    funeqi
    sylibr
    @5
    @7
    cX
    cY
    wceq
    #
    @4
    @15
    wn
    @3
    cX
    cY
    neneq
    adantl
    @5
    cX
    cY
    cpr
    #
    cZ
    cZ
    cpr
    #
    cF
    wf
    #
    @7
    @15
    @5
    @16
    @17
    @8
    wf
    #
    @18
    @5
    @12
    @19
    @14
    cX
    cY
    cZ
    cZ
    cU
    cV
    cW
    cW
    fprg
    syl
    @16
    @17
    @8
    cF
    cF
    @8
    fpropnf1.f
    eqcomi
    feq1i
    sylib
    @18
    @7
    wa
    @16
    @17
    cF
    wf1
    #
    @5
    @15
    @16
    @17
    cF
    df-f1
    @20
    @18
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    @16
    wral
    #
    vx
    @16
    wral
    #
    wa
    @5
    @15
    vx
    vy
    @16
    @17
    cF
    dff13
    @5
    @29
    @15
    @18
    @5
    @29
    cX
    cF
    cfv
    #
    @24
    wceq
    #
    cX
    @23
    wceq
    #
    wi
    #
    vy
    @16
    wral
    #
    cY
    cF
    cfv
    #
    @24
    wceq
    #
    cY
    @23
    wceq
    #
    wi
    #
    vy
    @16
    wral
    #
    wa
    #
    @15
    @3
    @29
    @40
    wb
    #
    @4
    @0
    @1
    @41
    @2
    @28
    @34
    @39
    vx
    cX
    cY
    cU
    cV
    @21
    cX
    wceq
    #
    @27
    @33
    vy
    @16
    @42
    @25
    @31
    @26
    @32
    @42
    @22
    @30
    @24
    @21
    cX
    cF
    fveq2
    eqeq1d
    @21
    cX
    @23
    eqeq1
    imbi12d
    ralbidv
    @21
    cY
    wceq
    #
    @27
    @38
    vy
    @16
    @43
    @25
    @36
    @26
    @37
    @43
    @22
    @35
    @24
    @21
    cY
    cF
    fveq2
    eqeq1d
    @21
    cY
    @23
    eqeq1
    imbi12d
    ralbidv
    ralprg
    3adant3
    adantr
    @5
    @40
    @30
    @30
    wceq
    #
    cX
    cX
    wceq
    #
    wi
    #
    @30
    @35
    wceq
    #
    @15
    wi
    #
    wa
    #
    @35
    @30
    wceq
    #
    cY
    cX
    wceq
    #
    wi
    #
    @35
    @35
    wceq
    #
    cY
    cY
    wceq
    #
    wi
    #
    wa
    #
    wa
    #
    @15
    @3
    @40
    @57
    wb
    #
    @4
    @0
    @1
    @58
    @2
    @10
    @34
    @49
    @39
    @56
    @33
    @46
    @48
    vy
    cX
    cY
    cU
    cV
    @23
    cX
    wceq
    #
    @31
    @44
    @32
    @45
    @59
    @24
    @30
    @30
    @23
    cX
    cF
    fveq2
    #
    eqeq2d
    @23
    cX
    cX
    eqeq2
    imbi12d
    @23
    cY
    wceq
    #
    @31
    @47
    @32
    @15
    @61
    @24
    @35
    @30
    @23
    cY
    cF
    fveq2
    #
    eqeq2d
    @23
    cY
    cX
    eqeq2
    imbi12d
    ralprg
    @38
    @52
    @55
    vy
    cX
    cY
    cU
    cV
    @59
    @36
    @50
    @37
    @51
    @59
    @24
    @30
    @35
    @60
    eqeq2d
    @23
    cX
    cY
    eqeq2
    imbi12d
    @61
    @36
    @53
    @37
    @54
    @61
    @24
    @35
    @35
    @62
    eqeq2d
    @23
    cY
    cY
    eqeq2
    imbi12d
    ralprg
    anbi12d
    3adant3
    adantr
    @5
    @49
    @15
    @56
    @5
    @48
    @15
    @46
    @5
    @47
    @15
    @15
    @5
    @30
    cZ
    @35
    @5
    @30
    cX
    @8
    cfv
    #
    cZ
    cX
    cF
    @8
    fpropnf1.f
    fveq1i
    @5
    @0
    @2
    @4
    w3a
    #
    @63
    cZ
    wceq
    @5
    @0
    @2
    wa
    #
    @4
    wa
    @64
    @3
    @65
    @4
    @0
    @1
    @2
    3simpb
    anim1i
    @0
    @2
    @4
    df-3an
    sylibr
    cX
    cY
    cZ
    cZ
    cU
    cW
    fvpr1g
    syl
    syl5eq
    @5
    @35
    cY
    @8
    cfv
    #
    cZ
    cY
    cF
    @8
    fpropnf1.f
    fveq1i
    @5
    @1
    @2
    @4
    w3a
    #
    @66
    cZ
    wceq
    @5
    @1
    @2
    wa
    #
    @4
    wa
    @67
    @3
    @68
    @4
    @0
    @1
    @2
    3simpc
    anim1i
    @1
    @2
    @4
    df-3an
    sylibr
    cX
    cY
    cZ
    cZ
    cV
    cW
    fvpr2g
    syl
    syl5req
    eqtrd
    @5
    @15
    idd
    embantd
    adantld
    adantrd
    sylbid
    sylbid
    adantld
    syl5bi
    syl5bir
    mpand
    mtod
    jca
end
