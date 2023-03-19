include "wcel.mm"
include "cv.mm"
include "cima.mm"
include "cdif.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "wceq.mm"
include "cres.mm"
include "ccnv.mm"
include "wfun.mm"
include "w3a.mm"
include "con0.mm"
include "wrex.mm"
include "wa.mm"
include "wn.mm"
include "cfv.mm"
include "df-ne.mm"
include "ralbii.mm"
include "wi.mm"
include "ralim.mm"
include "sylbi.mm"
include "syl5bir.mm"
include "cvv.mm"
include "tz7.48-3.mm"
include "elex.mm"
include "nsyl3.mm"
include "nsyli.mm"
include "dfrex2.mm"
include "syl6ibr.mm"
include "imaeq2.mm"
include "difeq2d.mm"
include "eqeq1d.mm"
include "onminex.mm"
include "syl6.mm"
include "anbi2i.mm"
include "rexbii.mm"
include "nfra1.mm"
include "nfxfr.mm"
include "simpllr.mm"
include "wss.mm"
include "wfn.mm"
include "fnfun.mm"
include "ax-mp.mm"
include "fvelima.mm"
include "mpan.mm"
include "nfv.mm"
include "nfan.mm"
include "rsp.mm"
include "adantld.mm"
include "onelon.mm"
include "neeq1d.mm"
include "fveq2.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl5bi.mm"
include "com23.mm"
include "syl.mm"
include "sylcom.mm"
include "com3r.mm"
include "imp.mm"
include "expcomd.mm"
include "eldifi.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "syl8.mm"
include "com34.mm"
include "rexlimd.mm"
include "syl5.mm"
include "ssrdv.mm"
include "ssdif0.mm"
include "biimpri.mm"
include "anim12i.mm"
include "eqss.mm"
include "sylibr.mm"
include "onss.mm"
include "ssel.mm"
include "cdm.mm"
include "fndm.mm"
include "syl6sseqr.mm"
include "funfvima2.mm"
include "sylancr.mm"
include "com12.mm"
include "a1i.mm"
include "syl10.mm"
include "imp4a.mm"
include "eldifn.mm"
include "eleq1a.mm"
include "con3d.mm"
include "syl5com.mm"
include "syldd.mm"
include "com4r.mm"
include "imp31.mm"
include "ralrimi.mm"
include "ex.mm"
include "ancld.mm"
include "tz7.48lem.mm"
include "syl56.mm"
include "ancoms.mm"
include "adantr.mm"
include "3jca.mm"
include "exp41.mm"
include "reximdai.mm"
include "syld.mm"
include "impcom.mm"

theorem tz7.49
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let vz: setvar z
  assume tz7.49.1: |- F Fn On
  assume tz7.49.2: |- ( ph <-> A. x e. On ( ( A \ ( F " x ) ) =/= (/) -> ( F ` x ) e. ( A \ ( F " x ) ) ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F x
  disjoint F y
  disjoint ph y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint F z
  disjoint ph z
  assert |- ( ( A e. B /\ ph ) -> E. x e. On ( A. y e. x ( A \ ( F " y ) ) =/= (/) /\ ( F " x ) = A /\ Fun `' ( F |` x ) ) )

  proof
    wph
    cA
    cB
    wcel
    #
    cA
    cF
    vy
    cv
    #
    cima
    #
    cdif
    #
    c0
    wne
    #
    vy
    vx
    cv
    #
    wral
    #
    cF
    @5
    cima
    #
    cA
    wceq
    #
    cF
    @5
    cres
    ccnv
    wfun
    #
    w3a
    #
    vx
    con0
    wrex
    #
    wph
    @0
    cA
    @7
    cdif
    #
    c0
    wceq
    #
    @6
    wa
    #
    vx
    con0
    wrex
    #
    @11
    wph
    @0
    @13
    @3
    c0
    wceq
    #
    wn
    #
    vy
    @5
    wral
    #
    wa
    #
    vx
    con0
    wrex
    #
    @15
    wph
    @0
    @13
    vx
    con0
    wrex
    #
    @20
    wph
    @0
    @13
    wn
    #
    vx
    con0
    wral
    #
    wn
    @21
    wph
    @23
    @5
    cF
    cfv
    #
    @12
    wcel
    #
    vx
    con0
    wral
    #
    @0
    @23
    @12
    c0
    wne
    #
    vx
    con0
    wral
    #
    wph
    @26
    @27
    @22
    vx
    con0
    @12
    c0
    df-ne
    ralbii
    wph
    @27
    @25
    wi
    #
    vx
    con0
    wral
    #
    @28
    @26
    wi
    tz7.49.2
    @27
    @25
    vx
    con0
    ralim
    sylbi
    syl5bir
    @26
    cA
    cvv
    wcel
    @0
    vx
    cA
    cF
    tz7.49.1
    tz7.48-3
    cA
    cB
    elex
    nsyl3
    nsyli
    @13
    vx
    con0
    dfrex2
    syl6ibr
    @13
    @16
    vx
    vy
    @5
    @1
    wceq
    #
    @12
    @3
    c0
    @31
    @7
    @2
    cA
    @5
    @1
    cF
    imaeq2
    difeq2d
    #
    eqeq1d
    onminex
    syl6
    @14
    @19
    vx
    con0
    @6
    @18
    @13
    @4
    @17
    vy
    @5
    @3
    c0
    df-ne
    ralbii
    anbi2i
    rexbii
    syl6ibr
    wph
    @14
    @10
    vx
    con0
    wph
    @30
    vx
    tz7.49.2
    @29
    vx
    con0
    nfra1
    nfxfr
    wph
    @5
    con0
    wcel
    #
    @13
    @6
    @10
    wph
    @33
    @6
    @13
    @10
    wph
    @6
    @33
    @13
    @10
    wi
    wph
    @6
    @33
    @13
    @10
    wph
    @6
    wa
    #
    @33
    wa
    #
    @13
    wa
    #
    @6
    @8
    @9
    wph
    @6
    @33
    @13
    simpllr
    @36
    @7
    cA
    wss
    #
    cA
    @7
    wss
    #
    wa
    @8
    @35
    @37
    @13
    @38
    @35
    vz
    @7
    cA
    @34
    @33
    vz
    cv
    #
    @7
    wcel
    #
    @39
    cA
    wcel
    #
    wi
    @34
    @40
    @33
    @41
    @40
    @1
    cF
    cfv
    #
    @39
    wceq
    #
    vy
    @5
    wrex
    #
    @34
    @33
    @41
    wi
    #
    cF
    wfun
    #
    @40
    @44
    cF
    con0
    wfn
    #
    @46
    tz7.49.1
    con0
    cF
    fnfun
    ax-mp
    #
    vy
    @39
    @5
    cF
    fvelima
    mpan
    @34
    @43
    @45
    vy
    @5
    wph
    @6
    vy
    wph
    vy
    nfv
    #
    @4
    vy
    @5
    nfra1
    #
    nfan
    @45
    vy
    nfv
    @34
    @1
    @5
    wcel
    #
    @33
    @43
    @41
    @34
    @51
    @33
    @42
    @3
    wcel
    #
    @43
    @41
    wi
    @34
    @33
    @51
    @52
    wph
    @6
    @33
    @51
    wa
    #
    @52
    wi
    @6
    @53
    wph
    @52
    @6
    @53
    @4
    wph
    @52
    wi
    #
    @6
    @51
    @4
    @33
    @4
    vy
    @5
    rsp
    #
    adantld
    @53
    @1
    con0
    wcel
    #
    @4
    @54
    wi
    @5
    @1
    onelon
    @56
    wph
    @4
    @52
    wph
    @30
    @56
    @4
    @52
    wi
    #
    tz7.49.2
    @29
    @57
    vx
    @1
    con0
    @31
    @27
    @4
    @25
    @52
    @31
    @12
    @3
    c0
    @32
    neeq1d
    @31
    @24
    @42
    @12
    @3
    @5
    @1
    cF
    fveq2
    @32
    eleq12d
    imbi12d
    rspcv
    syl5bi
    com23
    #
    syl
    sylcom
    com3r
    imp
    expcomd
    @52
    @42
    cA
    wcel
    @43
    @41
    @42
    cA
    @2
    eldifi
    @42
    @39
    cA
    eleq1
    syl5ibcom
    syl8
    com34
    rexlimd
    syl5
    com23
    imp
    ssrdv
    @38
    @13
    cA
    @7
    ssdif0
    biimpri
    anim12i
    @7
    cA
    eqss
    sylibr
    @35
    @9
    @13
    @34
    @33
    @9
    @6
    wph
    @33
    @9
    wi
    @33
    @5
    con0
    wss
    #
    @6
    wph
    wa
    #
    @59
    @42
    @39
    cF
    cfv
    #
    wceq
    #
    wn
    #
    vz
    @1
    wral
    #
    vy
    @5
    wral
    #
    wa
    @9
    @5
    onss
    @60
    @59
    @65
    @60
    @59
    @65
    @60
    @59
    wa
    #
    @64
    vy
    @5
    @60
    @59
    vy
    @6
    wph
    vy
    @50
    @49
    nfan
    @59
    vy
    nfv
    nfan
    @66
    @51
    @64
    @66
    @51
    wa
    #
    @63
    vz
    @1
    @67
    vz
    nfv
    @60
    @59
    @51
    @39
    @1
    wcel
    #
    @63
    wi
    @59
    @51
    @68
    @60
    @63
    @59
    @51
    @68
    @61
    @2
    wcel
    #
    @60
    @63
    wi
    @59
    @51
    @56
    @68
    @69
    wi
    #
    @5
    con0
    @1
    ssel
    #
    @56
    @46
    @1
    cF
    cdm
    #
    wss
    @70
    @48
    @56
    @1
    con0
    @72
    @1
    onss
    @47
    @72
    con0
    wceq
    tz7.49.1
    con0
    cF
    fndm
    ax-mp
    syl6sseqr
    @1
    @39
    cF
    funfvima2
    sylancr
    syl6
    @59
    @51
    @60
    @69
    @63
    @59
    @51
    @60
    @52
    @69
    @63
    wi
    @59
    @51
    @6
    wph
    @52
    @59
    @51
    @56
    @6
    @4
    @54
    @71
    @51
    @6
    @4
    wi
    wi
    @59
    @6
    @51
    @4
    @55
    com12
    a1i
    @58
    syl10
    imp4a
    @52
    @42
    @2
    wcel
    #
    wn
    @69
    @63
    @42
    cA
    @2
    eldifn
    @69
    @62
    @73
    @61
    @2
    @42
    eleq1a
    con3d
    syl5com
    syl8
    com34
    syldd
    com4r
    imp31
    ralrimi
    ex
    ralrimi
    ex
    ancld
    vy
    vz
    @5
    cF
    tz7.49.1
    tz7.48lem
    syl56
    ancoms
    imp
    adantr
    3jca
    exp41
    com23
    com34
    imp4a
    reximdai
    syld
    impcom
end
