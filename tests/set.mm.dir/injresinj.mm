include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "c1.mm"
include "cfzo.mm"
include "cres.mm"
include "ccnv.mm"
include "wfun.mm"
include "cfv.mm"
include "wne.mm"
include "w3a.mm"
include "cn0.mm"
include "wcel.mm"
include "cpr.mm"
include "cima.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wi.mm"
include "wf1.mm"
include "wa.mm"
include "wss.mm"
include "fzo0ss1.mm"
include "fzossfz.mm"
include "sstri.mm"
include "fssres.mm"
include "mpan2.mm"
include "biantrud.mm"
include "ancom.mm"
include "df-f1.mm"
include "bitr4i.mm"
include "syl6bb.mm"
include "cv.mm"
include "wral.mm"
include "simp-4r.mm"
include "dff13.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "equequ1.mm"
include "imbi12d.mm"
include "eqeq2d.mm"
include "equequ2.mm"
include "rspc2va.mm"
include "fvres.mm"
include "eqcomd.mm"
include "eqeqan12d.mm"
include "biimpd.mm"
include "imim1d.mm"
include "imp.mm"
include "2a1d.mm"
include "expcom.mm"
include "syl.mm"
include "ex.mm"
include "pm2.43a.mm"
include "wn.mm"
include "wo.mm"
include "ianor.mm"
include "eqcom.mm"
include "injresinjlem.mm"
include "imp41.mm"
include "syl6ib.mm"
include "syl5bi.mm"
include "ancomsd.mm"
include "exp41.mm"
include "jaoi.mm"
include "a1d.mm"
include "sylbi.mm"
include "pm2.61i.mm"
include "ralrimivv.mm"
include "adantl.mm"
include "com13.mm"
include "com24.mm"
include "impcom.mm"
include "sylanbrc.mm"
include "biantrurd.mm"
include "syl6bbr.mm"
include "mpbird.mm"
include "syl6bi.mm"
include "3imp.mm"
include "com12.mm"

theorem injresinj
  let cF: class F
  let cK: class K
  let cV: class V
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y


  assert |- ( K e. NN0 -> ( ( F : ( 0 ... K ) --> V /\ Fun `' ( F |` ( 1 ..^ K ) ) /\ ( F ` 0 ) =/= ( F ` K ) ) -> ( ( ( F " { 0 , K } ) i^i ( F " ( 1 ..^ K ) ) ) = (/) -> Fun `' F ) ) )

  proof
    cc0
    cK
    cfz
    co
    #
    cV
    cF
    wf
    #
    cF
    c1
    cK
    cfzo
    co
    #
    cres
    #
    ccnv
    wfun
    #
    cc0
    cF
    cfv
    cK
    cF
    cfv
    wne
    #
    w3a
    cK
    cn0
    wcel
    #
    cF
    cc0
    cK
    cpr
    cima
    cF
    @2
    cima
    cin
    c0
    wceq
    #
    cF
    ccnv
    wfun
    #
    wi
    #
    @1
    @4
    @5
    @6
    @9
    wi
    #
    @4
    @1
    @5
    @10
    wi
    #
    @1
    @4
    @2
    cV
    @3
    wf1
    #
    @1
    @11
    wi
    @1
    @4
    @4
    @2
    cV
    @3
    wf
    #
    wa
    #
    @12
    @1
    @13
    @4
    @1
    @2
    @0
    wss
    @13
    @2
    cc0
    cK
    cfzo
    co
    @0
    cK
    fzo0ss1
    cc0
    cK
    fzossfz
    sstri
    @0
    cV
    @2
    cF
    fssres
    mpan2
    biantrud
    @14
    @13
    @4
    wa
    @12
    @4
    @13
    ancom
    @2
    cV
    @3
    df-f1
    bitr4i
    syl6bb
    @12
    @1
    @5
    @6
    @9
    @12
    @1
    wa
    #
    @5
    wa
    @6
    wa
    #
    @7
    @8
    @16
    @7
    wa
    #
    @8
    @0
    cV
    cF
    wf1
    #
    @17
    @1
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
    @19
    @21
    wceq
    #
    wi
    #
    vy
    @0
    wral
    vx
    @0
    wral
    #
    @18
    @12
    @1
    @5
    @6
    @7
    simp-4r
    #
    @15
    @5
    @6
    @7
    @26
    @1
    @12
    @5
    @6
    @7
    @26
    wi
    #
    wi
    wi
    @1
    @6
    @5
    @12
    @28
    @1
    @6
    @5
    @12
    @28
    wi
    wi
    @12
    @5
    @1
    @6
    wa
    #
    @28
    @12
    @13
    vv
    cv
    #
    @3
    cfv
    #
    vw
    cv
    #
    @3
    cfv
    #
    wceq
    #
    @30
    @32
    wceq
    #
    wi
    #
    vw
    @2
    wral
    vv
    @2
    wral
    #
    wa
    @5
    @29
    @28
    wi
    wi
    #
    vv
    vw
    @2
    cV
    @3
    dff13
    @37
    @38
    @13
    @37
    @5
    @29
    @7
    @26
    @37
    @5
    wa
    @29
    wa
    @7
    wa
    @25
    vx
    vy
    @0
    @0
    @37
    @5
    @29
    @7
    @19
    @0
    wcel
    #
    @21
    @0
    wcel
    #
    wa
    #
    @25
    wi
    #
    @19
    @2
    wcel
    #
    @21
    @2
    wcel
    #
    wa
    #
    @37
    @5
    @29
    @7
    @42
    wi
    #
    wi
    wi
    #
    wi
    #
    @37
    @45
    @47
    @45
    @37
    @45
    @47
    wi
    #
    @45
    @37
    wa
    @19
    @3
    cfv
    #
    @21
    @3
    cfv
    #
    wceq
    #
    @24
    wi
    #
    @49
    @36
    @53
    @50
    @33
    wceq
    #
    @19
    @32
    wceq
    #
    wi
    vv
    vw
    @19
    @21
    @2
    @2
    @30
    @19
    wceq
    #
    @34
    @54
    @35
    @55
    @56
    @31
    @50
    @33
    @30
    @19
    @3
    fveq2
    eqeq1d
    vv
    vx
    vw
    equequ1
    imbi12d
    @32
    @21
    wceq
    #
    @54
    @52
    @55
    @24
    @57
    @33
    @51
    @50
    @32
    @21
    @3
    fveq2
    eqeq2d
    vw
    vy
    vx
    equequ2
    imbi12d
    rspc2va
    @45
    @53
    @47
    @45
    @53
    wa
    #
    @46
    @5
    @29
    @58
    @25
    @7
    @41
    @45
    @53
    @25
    @45
    @23
    @52
    @24
    @45
    @23
    @52
    @43
    @44
    @20
    @50
    @22
    @51
    @43
    @50
    @20
    @19
    @2
    cF
    fvres
    eqcomd
    @44
    @51
    @22
    @21
    @2
    cF
    fvres
    eqcomd
    eqeqan12d
    biimpd
    imim1d
    imp
    2a1d
    2a1d
    expcom
    syl
    ex
    pm2.43a
    @45
    wn
    @43
    wn
    #
    @44
    wn
    #
    wo
    #
    @48
    @43
    @44
    ianor
    @61
    @47
    @37
    @59
    @47
    @60
    @59
    @5
    @29
    @7
    @42
    @59
    @5
    wa
    #
    @29
    wa
    @7
    wa
    #
    @40
    @39
    @25
    @63
    @40
    @39
    wa
    #
    @25
    @23
    @22
    @20
    wceq
    #
    @63
    @64
    wa
    #
    @24
    @20
    @22
    eqcom
    @66
    @65
    @21
    @19
    wceq
    #
    @24
    @62
    @29
    @7
    @64
    @65
    @67
    wi
    #
    @59
    @5
    @29
    @7
    @64
    @68
    wi
    wi
    wi
    cF
    cK
    cV
    @21
    @19
    injresinjlem
    imp
    imp41
    @21
    @19
    eqcom
    syl6ib
    syl5bi
    ex
    ancomsd
    exp41
    cF
    cK
    cV
    @19
    @21
    injresinjlem
    jaoi
    a1d
    sylbi
    pm2.61i
    imp41
    ralrimivv
    exp41
    adantl
    sylbi
    com13
    ex
    com24
    impcom
    imp41
    vx
    vy
    @0
    cV
    cF
    dff13
    sylanbrc
    @17
    @8
    @1
    @8
    wa
    @18
    @17
    @1
    @8
    @27
    biantrurd
    @0
    cV
    cF
    df-f1
    syl6bbr
    mpbird
    ex
    exp41
    syl6bi
    pm2.43a
    3imp
    com12
end
