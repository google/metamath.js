include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "wn.mm"
include "cc0.mm"
include "cfz.mm"
include "wa.mm"
include "wf.mm"
include "cn0.mm"
include "cpr.mm"
include "cima.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cfv.mm"
include "wne.mm"
include "wi.mm"
include "wo.mm"
include "elfznelfzo.mm"
include "wnel.mm"
include "fvinim0ffz.mm"
include "df-nel.mm"
include "fveq2.mm"
include "eqcoms.mm"
include "eleq1d.mm"
include "notbid.mm"
include "biimpd.mm"
include "cv.mm"
include "wrex.mm"
include "wfn.mm"
include "wss.mm"
include "wb.mm"
include "ffn.mm"
include "cuz.mm"
include "1eluzge0.mm"
include "fzoss1.mm"
include "mp1i.mm"
include "fzossfz.mm"
include "syl6ss.mm"
include "fvelimab.mm"
include "syl2an.mm"
include "wral.mm"
include "ralnex.mm"
include "eqeq1d.mm"
include "rspcva.mm"
include "pm2.21.mm"
include "a1d.mm"
include "2a1d.mm"
include "syl.mm"
include "expcom.mm"
include "com24.mm"
include "sylbir.mm"
include "com12.mm"
include "sylbid.mm"
include "syl6com.mm"
include "sylbi.mm"
include "adantr.mm"
include "adantl.mm"
include "jaoi.mm"
include "com13.mm"
include "com14.mm"
include "com15.mm"
include "eqtr3.mm"
include "2a1.mm"
include "neeq12d.mm"
include "df-ne.mm"
include "pm2.24.mm"
include "syl6bi.mm"
include "ccase.mm"
include "ex.mm"
include "pm2.61i.mm"
include "com23.mm"
include "impcom.mm"
include "com25.mm"

theorem injresinjlem
  let cF: class F
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  let vz: setvar z


  assert |- ( -. Y e. ( 1 ..^ K ) -> ( ( F ` 0 ) =/= ( F ` K ) -> ( ( F : ( 0 ... K ) --> V /\ K e. NN0 ) -> ( ( ( F " { 0 , K } ) i^i ( F " ( 1 ..^ K ) ) ) = (/) -> ( ( X e. ( 0 ... K ) /\ Y e. ( 0 ... K ) ) -> ( ( F ` X ) = ( F ` Y ) -> X = Y ) ) ) ) ) )

  proof
    cY
    c1
    cK
    cfzo
    co
    #
    wcel
    wn
    #
    cX
    cc0
    cK
    cfz
    co
    #
    wcel
    #
    cY
    @2
    wcel
    #
    wa
    #
    @2
    cV
    cF
    wf
    #
    cK
    cn0
    wcel
    #
    wa
    #
    cF
    cc0
    cK
    cpr
    cima
    cF
    @0
    cima
    #
    cin
    c0
    wceq
    #
    cc0
    cF
    cfv
    #
    cK
    cF
    cfv
    #
    wne
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    wceq
    #
    cX
    cY
    wceq
    #
    wi
    #
    @5
    @1
    @8
    @10
    @13
    @18
    wi
    #
    wi
    wi
    #
    @4
    @3
    @1
    @20
    wi
    @4
    @1
    @3
    @20
    @4
    @1
    @3
    @20
    wi
    #
    @4
    @1
    wa
    cY
    cc0
    wceq
    #
    cY
    cK
    wceq
    #
    wo
    #
    @21
    cK
    cY
    elfznelfzo
    @3
    @24
    @20
    cX
    @0
    wcel
    #
    @3
    @24
    @20
    wi
    #
    wi
    @10
    @3
    @24
    @8
    @25
    @19
    @3
    @10
    @24
    @8
    @25
    @19
    wi
    #
    wi
    wi
    @8
    @10
    @24
    @3
    @27
    @8
    @10
    @11
    @9
    wnel
    #
    @12
    @9
    wnel
    #
    wa
    #
    @24
    @3
    @27
    wi
    #
    wi
    cF
    cK
    cV
    fvinim0ffz
    @24
    @30
    @8
    @31
    @22
    @30
    @8
    @31
    wi
    #
    wi
    @23
    @30
    @22
    @32
    @28
    @22
    @32
    wi
    #
    @29
    @28
    @11
    @9
    wcel
    #
    wn
    #
    @33
    @11
    @9
    df-nel
    @22
    @35
    @15
    @9
    wcel
    #
    wn
    #
    @32
    @22
    @35
    @37
    @22
    @34
    @36
    @22
    @11
    @15
    @9
    @11
    @15
    wceq
    #
    cc0
    cY
    cc0
    cY
    cF
    fveq2
    eqcoms
    #
    eleq1d
    notbid
    biimpd
    @8
    @37
    @31
    @8
    @37
    vz
    cv
    #
    cF
    cfv
    #
    @15
    wceq
    #
    vz
    @0
    wrex
    #
    wn
    #
    @31
    @8
    @36
    @43
    @6
    cF
    @2
    wfn
    @0
    @2
    wss
    @36
    @43
    wb
    @7
    @2
    cV
    cF
    ffn
    @7
    @0
    cc0
    cK
    cfzo
    co
    #
    @2
    c1
    cc0
    cuz
    cfv
    wcel
    @0
    @45
    wss
    @7
    1eluzge0
    c1
    cc0
    cK
    fzoss1
    mp1i
    cc0
    cK
    fzossfz
    syl6ss
    vz
    @2
    @0
    @15
    cF
    fvelimab
    syl2an
    notbid
    @44
    @8
    @31
    @44
    @42
    wn
    #
    vz
    @0
    wral
    #
    @32
    @42
    vz
    @0
    ralnex
    @47
    @25
    @3
    @8
    @19
    @25
    @47
    @3
    @8
    @19
    wi
    wi
    #
    @25
    @47
    wa
    @16
    wn
    #
    @48
    @46
    @49
    vz
    cX
    @0
    @40
    cX
    wceq
    #
    @42
    @16
    @50
    @41
    @14
    @15
    @40
    cX
    cF
    fveq2
    eqeq1d
    notbid
    rspcva
    @49
    @19
    @3
    @8
    @49
    @18
    @13
    @16
    @17
    pm2.21
    #
    a1d
    2a1d
    syl
    expcom
    com24
    sylbir
    com12
    sylbid
    com12
    #
    syl6com
    sylbi
    adantr
    com12
    @30
    @23
    @32
    @29
    @23
    @32
    wi
    #
    @28
    @29
    @12
    @9
    wcel
    #
    wn
    #
    @53
    @12
    @9
    df-nel
    @23
    @55
    @37
    @32
    @23
    @55
    @37
    @23
    @54
    @36
    @23
    @12
    @15
    @9
    @12
    @15
    wceq
    #
    cK
    cY
    cK
    cY
    cF
    fveq2
    eqcoms
    #
    eleq1d
    notbid
    biimpd
    @52
    syl6com
    sylbi
    adantl
    com12
    jaoi
    com13
    sylbid
    com14
    com12
    com15
    @3
    @25
    wn
    #
    @26
    @3
    @58
    wa
    cX
    cc0
    wceq
    #
    cX
    cK
    wceq
    #
    wo
    #
    @26
    cK
    cX
    elfznelfzo
    @61
    @24
    @20
    @59
    @22
    @60
    @23
    @20
    @59
    @22
    wa
    @17
    @20
    cX
    cY
    cc0
    eqtr3
    @17
    @19
    @8
    @10
    @17
    @13
    @16
    2a1
    2a1d
    #
    syl
    @60
    @22
    wa
    #
    @19
    @8
    @10
    @63
    @13
    @15
    @14
    wne
    #
    @18
    @63
    @11
    @15
    @12
    @14
    @22
    @38
    @60
    @39
    adantl
    @60
    @12
    @14
    wceq
    #
    @22
    @65
    cK
    cX
    cK
    cX
    cF
    fveq2
    eqcoms
    adantr
    neeq12d
    @64
    @15
    @14
    wceq
    #
    wn
    #
    @18
    @15
    @14
    df-ne
    @16
    @67
    @17
    @67
    @17
    wi
    @15
    @14
    @66
    @17
    pm2.24
    eqcoms
    com12
    sylbi
    syl6bi
    2a1d
    @59
    @23
    wa
    #
    @19
    @8
    @10
    @68
    @13
    @14
    @15
    wne
    #
    @18
    @68
    @11
    @14
    @12
    @15
    @59
    @11
    @14
    wceq
    #
    @23
    @70
    cc0
    cX
    cc0
    cX
    cF
    fveq2
    eqcoms
    adantr
    @23
    @56
    @59
    @57
    adantl
    neeq12d
    @69
    @49
    @18
    @14
    @15
    df-ne
    @51
    sylbi
    syl6bi
    2a1d
    @60
    @23
    wa
    @17
    @20
    cX
    cY
    cK
    eqtr3
    @62
    syl
    ccase
    ex
    syl
    expcom
    pm2.61i
    com12
    syl
    ex
    com23
    impcom
    com12
    com25
end
