include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "ctg.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "c2ndc.mm"
include "wcel.mm"
include "ctb.mm"
include "cima.mm"
include "cmpt.mm"
include "crn.mm"
include "ctop.mm"
include "wss.mm"
include "wel.mm"
include "wrex.mm"
include "wral.mm"
include "ccn.mm"
include "co.mm"
include "cntop2.mm"
include "syl.mm"
include "ad2antrr.mm"
include "wf.mm"
include "simplll.mm"
include "bastg.mm"
include "ad2antlr.mm"
include "simprr.mm"
include "sseqtrd.mm"
include "sselda.mm"
include "syl2anc.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "cuni.mm"
include "elunii.mm"
include "syl6eleqr.mm"
include "ancoms.mm"
include "adantl.mm"
include "ad3antrrr.mm"
include "eleqtrrd.mm"
include "wfn.mm"
include "wb.mm"
include "cnf.mm"
include "ffn.mm"
include "fvelrnb.mm"
include "3syl.mm"
include "mpbid.mm"
include "ccnv.mm"
include "simprll.mm"
include "cnima.mm"
include "adantr.mm"
include "simprrl.mm"
include "simprrr.mm"
include "simprlr.mm"
include "eqeltrd.mm"
include "adantrr.mm"
include "elpreima.mm"
include "mpbir2and.mm"
include "tg2.mm"
include "simprl.mm"
include "imaeq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "sylancl.mm"
include "cvv.mm"
include "wfun.mm"
include "fnfun.mm"
include "funimass2.mm"
include "vex.mm"
include "ssexg.mm"
include "elrnmpt.mm"
include "mpbird.mm"
include "cdm.mm"
include "wi.mm"
include "cnvimass.mm"
include "syl6ss.mm"
include "funfvima2.mm"
include "mpd.mm"
include "eqeltrrd.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "syl12anc.mm"
include "rexlimddv.mm"
include "anassrs.mm"
include "ralrimivva.mm"
include "basgen2.mm"
include "syl3anc.mm"
include "tgclb.mm"
include "sylibr.mm"
include "ccrd.mm"
include "wfo.mm"
include "con0.mm"
include "omelon.mm"
include "ondomen.mm"
include "sylancr.mm"
include "dffn4.mm"
include "sylib.mm"
include "fodomnum.mm"
include "sylc.mm"
include "domtr.mm"
include "2ndci.mm"
include "is2ndc.mm"
include "r19.29a.mm"

theorem 2ndcomap
  let wph: wff ph
  let vx: setvar x
  let cF: class F
  let cJ: class J
  let cK: class K
  let cY: class Y
  let vk: setvar k
  let vm: setvar m
  let vt: setvar t
  let vw: setvar w
  let vz: setvar z
  let vb: setvar b
  assume 2ndcomap.2: |- Y = U. K
  assume 2ndcomap.3: |- ( ph -> J e. 2ndc )
  assume 2ndcomap.5: |- ( ph -> F e. ( J Cn K ) )
  assume 2ndcomap.6: |- ( ph -> ran F = Y )
  assume 2ndcomap.7: |- ( ( ph /\ x e. J ) -> ( F " x ) e. K )

  disjoint F x
  disjoint J x
  disjoint ph x
  disjoint K x
  disjoint k m
  disjoint k t
  disjoint k w
  disjoint k x
  disjoint k z
  disjoint F k
  disjoint m t
  disjoint m w
  disjoint m x
  disjoint m z
  disjoint F m
  disjoint t w
  disjoint t x
  disjoint t z
  disjoint F t
  disjoint w x
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint F z
  disjoint b k
  disjoint b m
  disjoint b t
  disjoint b x
  disjoint b z
  disjoint J b
  disjoint J k
  disjoint J m
  disjoint J t
  disjoint J z
  disjoint b ph
  disjoint k ph
  disjoint m ph
  disjoint ph t
  disjoint ph z
  disjoint b w
  disjoint K b
  disjoint K k
  disjoint K m
  disjoint K t
  disjoint K w
  disjoint K z
  assert |- ( ph -> K e. 2ndc )

  proof
    wph
    vb
    cv
    #
    com
    cdom
    wbr
    #
    @0
    ctg
    cfv
    #
    cJ
    wceq
    #
    wa
    #
    cK
    c2ndc
    wcel
    vb
    ctb
    wph
    @0
    ctb
    wcel
    #
    wa
    #
    @4
    wa
    #
    vx
    @0
    cF
    vx
    cv
    #
    cima
    #
    cmpt
    #
    crn
    #
    ctg
    cfv
    #
    cK
    c2ndc
    @7
    cK
    ctop
    wcel
    #
    @11
    cK
    wss
    #
    vz
    vw
    wel
    #
    vw
    cv
    #
    vk
    cv
    #
    wss
    #
    wa
    #
    vw
    @11
    wrex
    #
    vz
    @17
    wral
    vk
    cK
    wral
    @12
    cK
    wceq
    wph
    @13
    @5
    @4
    wph
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    @13
    2ndcomap.5
    cF
    cJ
    cK
    cntop2
    syl
    ad2antrr
    #
    @7
    @0
    cK
    @10
    wf
    #
    @14
    @7
    vx
    @0
    @9
    cK
    @10
    @7
    vx
    vb
    wel
    #
    wa
    wph
    @8
    cJ
    wcel
    @9
    cK
    wcel
    wph
    @5
    @4
    @24
    simplll
    @7
    @0
    cJ
    @8
    @7
    @0
    @2
    cJ
    @5
    @0
    @2
    wss
    wph
    @4
    @0
    ctb
    bastg
    ad2antlr
    @6
    @1
    @3
    simprr
    #
    sseqtrd
    sselda
    2ndcomap.7
    syl2anc
    @10
    eqid
    #
    fmptd
    #
    @0
    cK
    @10
    frn
    syl
    @7
    @20
    vk
    vz
    cK
    @17
    @7
    @17
    cK
    wcel
    #
    vz
    vk
    wel
    #
    wa
    #
    wa
    #
    vt
    cv
    #
    cF
    cfv
    #
    vz
    cv
    #
    wceq
    #
    @20
    vt
    cJ
    cuni
    #
    @31
    @34
    cF
    crn
    #
    wcel
    #
    @35
    vt
    @36
    wrex
    #
    @31
    @34
    cY
    @37
    @30
    @34
    cY
    wcel
    #
    @7
    @29
    @28
    @40
    @29
    @28
    wa
    @34
    cK
    cuni
    cY
    @34
    @17
    cK
    elunii
    2ndcomap.2
    syl6eleqr
    ancoms
    adantl
    wph
    @37
    cY
    wceq
    @5
    @4
    @30
    2ndcomap.6
    ad3antrrr
    eleqtrrd
    @31
    @36
    cY
    cF
    wf
    #
    cF
    @36
    wfn
    #
    @38
    @39
    wb
    wph
    @41
    @5
    @4
    @30
    wph
    @21
    @41
    2ndcomap.5
    cF
    cJ
    cK
    @36
    cY
    @36
    eqid
    2ndcomap.2
    cnf
    syl
    ad3antrrr
    #
    @36
    cY
    cF
    ffn
    #
    vt
    @36
    @34
    cF
    fvelrnb
    3syl
    mpbid
    @7
    @30
    @32
    @36
    wcel
    #
    @35
    wa
    #
    @20
    @7
    @30
    @46
    wa
    #
    wa
    #
    vt
    vm
    wel
    #
    vm
    cv
    #
    cF
    ccnv
    @17
    cima
    #
    wss
    #
    wa
    #
    @20
    vm
    @0
    @48
    @51
    @2
    wcel
    @32
    @51
    wcel
    #
    @53
    vm
    @0
    wrex
    @48
    @51
    cJ
    @2
    @48
    @21
    @28
    @51
    cJ
    wcel
    wph
    @21
    @5
    @4
    @47
    2ndcomap.5
    ad3antrrr
    @7
    @28
    @29
    @46
    simprll
    @17
    cF
    cJ
    cK
    cnima
    syl2anc
    @7
    @3
    @47
    @25
    adantr
    eleqtrrd
    @48
    @54
    @45
    @33
    @17
    wcel
    #
    @7
    @30
    @45
    @35
    simprrl
    @48
    @33
    @34
    @17
    @7
    @30
    @45
    @35
    simprrr
    #
    @7
    @28
    @29
    @46
    simprlr
    eqeltrd
    @48
    @42
    @54
    @45
    @55
    wa
    wb
    @7
    @30
    @42
    @46
    @31
    @41
    @42
    @43
    @44
    syl
    adantrr
    #
    @36
    @32
    @17
    cF
    elpreima
    syl
    mpbir2and
    vm
    @51
    @0
    @32
    tg2
    syl2anc
    @48
    vm
    vb
    wel
    #
    @53
    wa
    #
    wa
    #
    cF
    @50
    cima
    #
    @11
    wcel
    #
    @34
    @61
    wcel
    #
    @61
    @17
    wss
    #
    @20
    @60
    @62
    @61
    @9
    wceq
    #
    vx
    @0
    wrex
    #
    @60
    @58
    @61
    @61
    wceq
    #
    @66
    @48
    @58
    @53
    simprl
    @61
    eqid
    @65
    @67
    vx
    @50
    @0
    @8
    @50
    wceq
    @9
    @61
    @61
    @8
    @50
    cF
    imaeq2
    eqeq2d
    rspcev
    sylancl
    @60
    @61
    cvv
    wcel
    #
    @62
    @66
    wb
    @60
    @64
    @17
    cvv
    wcel
    @68
    @60
    cF
    wfun
    #
    @52
    @64
    @60
    @42
    @69
    @48
    @42
    @59
    @57
    adantr
    @36
    cF
    fnfun
    syl
    #
    @48
    @58
    @49
    @52
    simprrr
    #
    @50
    @17
    cF
    funimass2
    syl2anc
    #
    vk
    vex
    @61
    @17
    cvv
    ssexg
    sylancl
    vx
    @0
    @9
    @61
    @10
    cvv
    @26
    elrnmpt
    syl
    mpbird
    @60
    @33
    @34
    @61
    @48
    @35
    @59
    @56
    adantr
    @60
    @49
    @33
    @61
    wcel
    #
    @48
    @58
    @49
    @52
    simprrl
    @60
    @69
    @50
    cF
    cdm
    #
    wss
    @49
    @73
    wi
    @70
    @60
    @50
    @51
    @74
    @71
    cF
    @17
    cnvimass
    syl6ss
    @50
    @32
    cF
    funfvima2
    syl2anc
    mpd
    eqeltrrd
    @72
    @19
    @63
    @64
    wa
    vw
    @61
    @11
    @16
    @61
    wceq
    @15
    @63
    @18
    @64
    @16
    @61
    @34
    eleq2
    @16
    @61
    @17
    sseq1
    anbi12d
    rspcev
    syl12anc
    rexlimddv
    anassrs
    rexlimddv
    ralrimivva
    vk
    vz
    vw
    @11
    cK
    basgen2
    syl3anc
    #
    @7
    @11
    ctb
    wcel
    #
    @11
    com
    cdom
    wbr
    #
    @12
    c2ndc
    wcel
    @7
    @12
    ctop
    wcel
    @76
    @7
    @12
    cK
    ctop
    @75
    @22
    eqeltrd
    @11
    tgclb
    sylibr
    @7
    @11
    @0
    cdom
    wbr
    #
    @1
    @77
    @7
    @0
    ccrd
    cdm
    wcel
    #
    @0
    @11
    @10
    wfo
    #
    @78
    @7
    com
    con0
    wcel
    @1
    @79
    omelon
    @6
    @1
    @3
    simprl
    #
    com
    @0
    ondomen
    sylancr
    @7
    @10
    @0
    wfn
    #
    @80
    @7
    @23
    @82
    @27
    @0
    cK
    @10
    ffn
    syl
    @0
    @10
    dffn4
    sylib
    @0
    @11
    @10
    fodomnum
    sylc
    @81
    @11
    @0
    com
    domtr
    syl2anc
    @11
    2ndci
    syl2anc
    eqeltrrd
    wph
    cJ
    c2ndc
    wcel
    @4
    vb
    ctb
    wrex
    2ndcomap.3
    vb
    cJ
    is2ndc
    sylib
    r19.29a
end
