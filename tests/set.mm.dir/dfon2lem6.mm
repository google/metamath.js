include "wtr.mm"
include "cv.mm"
include "wpss.mm"
include "wa.mm"
include "wel.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "wcel.mm"
include "weq.mm"
include "wo.mm"
include "cdif.mm"
include "wss.mm"
include "wn.mm"
include "pssss.mm"
include "ssralv.mm"
include "syl.mm"
include "impcom.mm"
include "adantrr.mm"
include "ad2ant2lr.mm"
include "psseq2.mm"
include "anbi1d.mm"
include "elequ2.mm"
include "imbi12d.mm"
include "albidv.mm"
include "rspccv.mm"
include "imp.mm"
include "eldifi.mm"
include "rspcv.mm"
include "psseq1.mm"
include "treq.mm"
include "anbi12d.mm"
include "elequ1.mm"
include "cbvalv.mm"
include "syl6ib.mm"
include "ad2ant2l.mm"
include "adantr.mm"
include "w3o.mm"
include "vex.mm"
include "dfon2lem5.mm"
include "3orrot.mm"
include "3orass.mm"
include "bitri.mm"
include "eleq1a.mm"
include "elndif.mm"
include "nsyli.mm"
include "adantll.mm"
include "orel1.mm"
include "trss.mm"
include "eldifn.mm"
include "ssel.mm"
include "con3d.mm"
include "syl5com.mm"
include "syl9.mm"
include "adantl.mm"
include "imp31.mm"
include "syl9r.mm"
include "mpd.mm"
include "syl5bi.mm"
include "syl5.mm"
include "mp2and.mm"
include "ex.mm"
include "ssrdv.mm"
include "dfpss2.mm"
include "spv.mm"
include "expd.mm"
include "com23.mm"
include "syl6.mm"
include "com3l.mm"
include "adantld.mm"
include "imp32.mm"
include "syl5bir.mm"
include "mpand.mm"
include "orrd.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "wrex.mm"
include "c0.mm"
include "wne.mm"
include "pssdif.mm"
include "r19.2z.mm"
include "ad2antrl.mm"
include "eleq1.mm"
include "syl5ibr.mm"
include "a1i.mm"
include "trel.mm"
include "syl7.mm"
include "ad2antrr.mm"
include "jaod.mm"
include "rexlimdv.mm"
include "syld.mm"
include "alrimiv.mm"

theorem dfon2lem6
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cS: class S
  let vw: setvar w
  let vs: setvar s
  let vt: setvar t

  disjoint S x
  disjoint S y
  disjoint S z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint S w
  disjoint S s
  disjoint S t
  disjoint w x
  disjoint s x
  disjoint t x
  disjoint w y
  disjoint s y
  disjoint t y
  disjoint w z
  disjoint s z
  disjoint t z
  disjoint s w
  disjoint t w
  disjoint s t
  assert |- ( ( Tr S /\ A. x e. S A. z ( ( z C. x /\ Tr z ) -> z e. x ) ) -> A. y ( ( y C. S /\ Tr y ) -> y e. S ) )

  proof
    cS
    wtr
    #
    vz
    cv
    #
    vx
    cv
    #
    wpss
    #
    @1
    wtr
    #
    wa
    #
    vz
    vx
    wel
    #
    wi
    #
    vz
    wal
    #
    vx
    cS
    wral
    #
    wa
    #
    vy
    cv
    #
    cS
    wpss
    #
    @11
    wtr
    #
    wa
    #
    @11
    cS
    wcel
    #
    wi
    vy
    @10
    @14
    @15
    @10
    @14
    wa
    #
    vy
    vs
    weq
    #
    vy
    vs
    wel
    #
    wo
    #
    vs
    cS
    @11
    cdif
    #
    wral
    #
    @15
    @16
    @19
    vs
    @20
    @10
    @14
    vs
    cv
    #
    @20
    wcel
    #
    @19
    @10
    @14
    @23
    wa
    #
    wa
    #
    @17
    @18
    @25
    @11
    @22
    wss
    #
    @17
    wn
    #
    @18
    @25
    vw
    @11
    @22
    @25
    vw
    vy
    wel
    #
    vw
    vs
    wel
    #
    @25
    @28
    wa
    #
    @1
    vw
    cv
    #
    wpss
    #
    @4
    wa
    #
    vz
    vw
    wel
    #
    wi
    #
    vz
    wal
    #
    vt
    cv
    #
    @22
    wpss
    #
    @37
    wtr
    #
    wa
    #
    vt
    vs
    wel
    #
    wi
    #
    vt
    wal
    #
    @29
    @25
    @28
    @36
    @25
    @8
    vx
    @11
    wral
    #
    @28
    @36
    wi
    @9
    @14
    @44
    @0
    @23
    @9
    @12
    @44
    @13
    @12
    @9
    @44
    @12
    @11
    cS
    wss
    @9
    @44
    wi
    @11
    cS
    pssss
    @8
    vx
    @11
    cS
    ssralv
    syl
    impcom
    adantrr
    ad2ant2lr
    @8
    @36
    vx
    @31
    @11
    vx
    vw
    weq
    #
    @7
    @35
    vz
    @45
    @5
    @33
    @6
    @34
    @45
    @3
    @32
    @4
    @2
    @31
    @1
    psseq2
    anbi1d
    vx
    vw
    vz
    elequ2
    imbi12d
    albidv
    rspccv
    syl
    imp
    @25
    @43
    @28
    @9
    @23
    @43
    @0
    @14
    @23
    @9
    @43
    @23
    @9
    @1
    @22
    wpss
    #
    @4
    wa
    #
    vz
    vs
    wel
    #
    wi
    #
    vz
    wal
    #
    @43
    @23
    @22
    cS
    wcel
    #
    @9
    @50
    wi
    @22
    cS
    @11
    eldifi
    #
    @8
    @50
    vx
    @22
    cS
    vx
    vs
    weq
    #
    @7
    @49
    vz
    @53
    @5
    @47
    @6
    @48
    @53
    @3
    @46
    @4
    @2
    @22
    @1
    psseq2
    anbi1d
    vx
    vs
    vz
    elequ2
    imbi12d
    albidv
    rspcv
    syl
    #
    @49
    @42
    vz
    vt
    vz
    vt
    weq
    #
    @47
    @40
    @48
    @41
    @55
    @46
    @38
    @4
    @39
    @1
    @37
    @22
    psseq1
    @1
    @37
    treq
    anbi12d
    vz
    vt
    vs
    elequ1
    imbi12d
    cbvalv
    syl6ib
    impcom
    ad2ant2l
    adantr
    @36
    @43
    wa
    @29
    vw
    vs
    weq
    #
    vs
    vw
    wel
    #
    w3o
    #
    @30
    @29
    vz
    vt
    @31
    @22
    vw
    vex
    vs
    vex
    dfon2lem5
    @58
    @56
    @57
    @29
    wo
    #
    wo
    #
    @30
    @29
    @58
    @56
    @57
    @29
    w3o
    @60
    @29
    @56
    @57
    3orrot
    @56
    @57
    @29
    3orass
    bitri
    @30
    @56
    wn
    #
    @60
    @29
    wi
    @24
    @28
    @61
    @10
    @23
    @28
    @61
    @14
    @23
    @28
    @61
    @23
    @56
    @31
    @20
    wcel
    @28
    @22
    @20
    @31
    eleq1a
    @31
    @11
    cS
    elndif
    nsyli
    imp
    adantll
    adantll
    @61
    @60
    @59
    @30
    @29
    @56
    @59
    orel1
    @30
    @57
    wn
    #
    @59
    @29
    wi
    @24
    @28
    @62
    @10
    @14
    @23
    @28
    @62
    @13
    @23
    @28
    @62
    wi
    wi
    @12
    @13
    @28
    @31
    @11
    wss
    #
    @23
    @62
    @11
    @31
    trss
    @23
    vs
    vy
    wel
    #
    wn
    @63
    @62
    @22
    cS
    @11
    eldifn
    @63
    @57
    @64
    @31
    @11
    @22
    ssel
    con3d
    syl5com
    syl9
    adantl
    imp31
    adantll
    @57
    @29
    orel1
    syl
    syl9r
    mpd
    syl5bi
    syl5
    mp2and
    ex
    ssrdv
    @26
    @27
    wa
    @11
    @22
    wpss
    #
    @25
    @18
    @11
    @22
    dfpss2
    @10
    @14
    @23
    @65
    @18
    wi
    #
    @9
    @14
    @23
    @66
    wi
    #
    wi
    @0
    @9
    @13
    @67
    @12
    @23
    @9
    @13
    @66
    @23
    @9
    @50
    @13
    @66
    wi
    @54
    @50
    @65
    @13
    @18
    @50
    @65
    @13
    @18
    @49
    @65
    @13
    wa
    #
    @18
    wi
    vz
    vy
    vz
    vy
    weq
    #
    @47
    @68
    @48
    @18
    @69
    @46
    @65
    @4
    @13
    @1
    @11
    @22
    psseq1
    @1
    @11
    treq
    anbi12d
    vz
    vy
    vs
    elequ1
    imbi12d
    spv
    expd
    com23
    syl6
    com3l
    adantld
    adantl
    imp32
    syl5bir
    mpand
    orrd
    anassrs
    ralrimiva
    @16
    @21
    @19
    vs
    @20
    wrex
    #
    @15
    @12
    @21
    @70
    wi
    #
    @10
    @13
    @12
    @20
    c0
    wne
    #
    @71
    @11
    cS
    pssdif
    @72
    @21
    @70
    @19
    vs
    @20
    r19.2z
    ex
    syl
    ad2antrl
    @16
    @19
    @15
    vs
    @20
    @16
    @19
    @23
    @15
    @16
    @17
    @23
    @15
    wi
    #
    @18
    @17
    @73
    wi
    @16
    @23
    @15
    @17
    @51
    @52
    @11
    @22
    cS
    eleq1
    syl5ibr
    a1i
    @0
    @18
    @73
    wi
    @9
    @14
    @23
    @51
    @0
    @18
    @15
    @52
    @0
    @18
    @51
    @15
    cS
    @11
    @22
    trel
    expd
    syl7
    ad2antrr
    jaod
    com23
    rexlimdv
    syld
    mpd
    ex
    alrimiv
end
