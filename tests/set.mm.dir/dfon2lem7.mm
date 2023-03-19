include "cv.mm"
include "wpss.mm"
include "wtr.mm"
include "wa.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wss.mm"
include "wel.mm"
include "wral.mm"
include "w3a.mm"
include "cab.mm"
include "cuni.mm"
include "wceq.mm"
include "csuc.mm"
include "csn.mm"
include "wn.mm"
include "weq.mm"
include "elequ1.mm"
include "elequ2.mm"
include "bitrd.mm"
include "notbid.mm"
include "cbvralv.mm"
include "biimpi.mm"
include "ralimi.mm"
include "untuni.mm"
include "sylibr.mm"
include "vex.mm"
include "sseq1.mm"
include "treq.mm"
include "raleq.mm"
include "3anbi123d.mm"
include "elab.mm"
include "cvv.mm"
include "dfon2lem3.mm"
include "ax-mp.mm"
include "simprd.mm"
include "untelirr.mm"
include "syl.mm"
include "3ad2ant3.mm"
include "sylbi.mm"
include "mprg.mm"
include "psseq2.mm"
include "anbi1d.mm"
include "imbi12d.mm"
include "albidv.mm"
include "3anbi3i.mm"
include "abbii.mm"
include "unieqi.mm"
include "eleq2i.mm"
include "sylnib.mm"
include "dfon2lem2.mm"
include "ssexi.mm"
include "snss.mm"
include "mtbi.mm"
include "intnan.mm"
include "cun.mm"
include "df-suc.mm"
include "sseq1i.mm"
include "unss.mm"
include "bitr4i.mm"
include "mtbir.mm"
include "dfon2lem1.mm"
include "suctr.mm"
include "wo.mm"
include "elsuc.mm"
include "wrex.mm"
include "eluni2.mm"
include "nfa1.mm"
include "rspccv.mm"
include "psseq1.mm"
include "anbi12d.mm"
include "cbvalv.mm"
include "syl6ib.mm"
include "rexlimi.mm"
include "rexlimiv.mm"
include "rgen.mm"
include "dfon2lem6.mm"
include "mp2an.mm"
include "eleq2.mm"
include "mpbiri.mm"
include "jaoi.mm"
include "sucex.mm"
include "elssuni.mm"
include "sylbir.mm"
include "mp3an23.mm"
include "ralbii.mm"
include "syl6bb.mm"
include "cbvabv.mm"
include "syl6sseq.mm"
include "a1i.mm"
include "syl5bir.mm"
include "mpani.mm"
include "syl5bi.mm"
include "mtoi.mm"
include "eleq1.mm"
include "spcv.mm"
include "mpan2i.mm"
include "mtod.mm"
include "dfpss2.mm"
include "biimpri.mm"
include "mpan.mm"
include "nsyl2.mm"
include "rsp.mm"
include "mpbii.mm"
include "3syl.mm"

theorem dfon2lem7
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  let vw: setvar w
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  assume dfon2lem7.1: |- A e. _V

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint A z
  disjoint A w
  disjoint A s
  disjoint A t
  disjoint A u
  disjoint x z
  disjoint w x
  disjoint s x
  disjoint t x
  disjoint u x
  disjoint y z
  disjoint w y
  disjoint s y
  disjoint t y
  disjoint u y
  disjoint w z
  disjoint s z
  disjoint t z
  disjoint u z
  disjoint s w
  disjoint t w
  disjoint u w
  disjoint s t
  disjoint s u
  disjoint t u
  disjoint B z
  disjoint B w
  disjoint B t
  assert |- ( A. x ( ( x C. A /\ Tr x ) -> x e. A ) -> ( B e. A -> A. y ( ( y C. B /\ Tr y ) -> y e. B ) ) )

  proof
    vx
    cv
    #
    cA
    wpss
    #
    @0
    wtr
    #
    wa
    #
    @0
    cA
    wcel
    #
    wi
    #
    vx
    wal
    #
    vw
    cv
    #
    cA
    wss
    #
    @7
    wtr
    #
    vy
    cv
    #
    vt
    cv
    #
    wpss
    #
    @10
    wtr
    #
    wa
    #
    vy
    vt
    wel
    #
    wi
    #
    vy
    wal
    #
    vt
    @7
    wral
    #
    w3a
    #
    vw
    cab
    #
    cuni
    #
    cA
    wceq
    #
    @10
    vz
    cv
    #
    wpss
    #
    @13
    wa
    #
    vy
    vz
    wel
    #
    wi
    #
    vy
    wal
    #
    vz
    cA
    wral
    #
    cB
    cA
    wcel
    @10
    cB
    wpss
    #
    @13
    wa
    #
    @10
    cB
    wcel
    #
    wi
    #
    vy
    wal
    #
    wi
    @6
    @21
    cA
    wpss
    #
    @22
    @6
    @35
    @21
    cA
    wcel
    #
    @6
    @36
    @21
    csuc
    #
    @8
    @9
    @10
    vu
    cv
    #
    wpss
    #
    @13
    wa
    #
    vy
    vu
    wel
    #
    wi
    #
    vy
    wal
    #
    vu
    @7
    wral
    #
    w3a
    #
    vw
    cab
    #
    cuni
    #
    wss
    #
    @48
    @21
    @47
    wss
    #
    @21
    csn
    #
    @47
    wss
    #
    wa
    #
    @51
    @49
    @21
    @47
    wcel
    #
    @51
    vz
    vz
    wel
    #
    wn
    #
    vz
    @21
    wral
    #
    @53
    wn
    vt
    vt
    wel
    #
    wn
    #
    vt
    @0
    wral
    #
    @56
    vx
    @20
    @59
    vx
    @20
    wral
    @55
    vz
    @0
    wral
    #
    vx
    @20
    wral
    @56
    @59
    @60
    vx
    @20
    @59
    @60
    @58
    @55
    vt
    vz
    @0
    vt
    vz
    weq
    #
    @57
    @54
    @61
    @57
    vz
    vt
    wel
    @54
    vt
    vz
    vt
    elequ1
    vt
    vz
    vz
    elequ2
    bitrd
    notbid
    cbvralv
    biimpi
    ralimi
    vz
    vx
    @20
    untuni
    sylibr
    @0
    @20
    wcel
    #
    @0
    cA
    wss
    #
    @2
    @17
    vt
    @0
    wral
    #
    w3a
    #
    @59
    @19
    @65
    vw
    @0
    vx
    vex
    #
    vw
    vx
    weq
    #
    @8
    @63
    @9
    @2
    @18
    @64
    @7
    @0
    cA
    sseq1
    #
    @7
    @0
    treq
    #
    @17
    vt
    @7
    @0
    raleq
    #
    3anbi123d
    elab
    #
    @64
    @63
    @59
    @2
    @17
    @58
    vt
    @0
    @17
    vu
    vu
    wel
    wn
    vu
    @11
    wral
    #
    @58
    @17
    @11
    wtr
    #
    @72
    @11
    cvv
    wcel
    @17
    @73
    @72
    wa
    wi
    vt
    vex
    vy
    vu
    @11
    cvv
    dfon2lem3
    ax-mp
    simprd
    vu
    @11
    untelirr
    syl
    ralimi
    3ad2ant3
    sylbi
    mprg
    @56
    @21
    @21
    wcel
    @53
    vz
    @21
    untelirr
    @21
    @47
    @21
    @20
    @46
    @19
    @45
    vw
    @18
    @44
    @8
    @9
    @17
    @43
    vt
    vu
    @7
    vt
    vu
    weq
    #
    @16
    @42
    vy
    @74
    @14
    @40
    @15
    @41
    @74
    @12
    @39
    @13
    @11
    @38
    @10
    psseq2
    anbi1d
    vt
    vu
    vy
    elequ2
    imbi12d
    albidv
    #
    cbvralv
    3anbi3i
    abbii
    unieqi
    eleq2i
    sylnib
    ax-mp
    @21
    @47
    @21
    cA
    dfon2lem7.1
    @9
    @18
    vw
    cA
    dfon2lem2
    #
    ssexi
    #
    snss
    mtbi
    intnan
    @48
    @21
    @50
    cun
    #
    @47
    wss
    @52
    @37
    @78
    @47
    @21
    df-suc
    #
    sseq1i
    @21
    @50
    @47
    unss
    bitr4i
    mtbir
    @36
    @50
    cA
    wss
    #
    @6
    @48
    @21
    cA
    @77
    snss
    @6
    @21
    cA
    wss
    #
    @80
    @48
    @76
    @81
    @80
    wa
    #
    @37
    cA
    wss
    #
    @6
    @48
    @83
    @78
    cA
    wss
    @82
    @37
    @78
    cA
    @79
    sseq1i
    @21
    @50
    cA
    unss
    bitr4i
    @83
    @48
    wi
    @6
    @83
    @37
    vs
    cv
    #
    cA
    wss
    #
    @84
    wtr
    #
    @0
    @38
    wpss
    #
    @2
    wa
    #
    vx
    vu
    wel
    #
    wi
    #
    vx
    wal
    #
    vu
    @84
    wral
    #
    w3a
    #
    vs
    cab
    #
    cuni
    #
    @47
    @83
    @37
    wtr
    #
    @91
    vu
    @37
    wral
    #
    @37
    @95
    wss
    #
    @21
    wtr
    #
    @96
    @8
    @18
    vw
    dfon2lem1
    #
    @21
    suctr
    ax-mp
    @91
    vu
    @37
    @38
    @37
    wcel
    @38
    @21
    wcel
    #
    @38
    @21
    wceq
    #
    wo
    @91
    @38
    @21
    vu
    vex
    elsuc
    @101
    @91
    @102
    @101
    vu
    vx
    wel
    #
    vx
    @20
    wrex
    #
    @91
    vx
    @38
    @20
    eluni2
    #
    @103
    @91
    vx
    @20
    @90
    vx
    nfa1
    @62
    @65
    @103
    @91
    wi
    #
    @71
    @64
    @63
    @106
    @2
    @64
    @103
    @43
    @91
    @17
    @43
    vt
    @38
    @0
    @75
    rspccv
    #
    @42
    @90
    vy
    vx
    vy
    vx
    weq
    #
    @40
    @88
    @41
    @89
    @108
    @39
    @87
    @13
    @2
    @10
    @0
    @38
    psseq1
    @10
    @0
    treq
    anbi12d
    vy
    vx
    vu
    elequ1
    imbi12d
    cbvalv
    syl6ib
    3ad2ant3
    sylbi
    rexlimi
    sylbi
    @102
    @91
    @0
    @21
    wpss
    #
    @2
    wa
    #
    @0
    @21
    wcel
    #
    wi
    #
    vx
    wal
    #
    @99
    @23
    @38
    wpss
    #
    @23
    wtr
    #
    wa
    #
    vz
    vu
    wel
    #
    wi
    #
    vz
    wal
    #
    vu
    @21
    wral
    @113
    @100
    @119
    vu
    @21
    @101
    @104
    @119
    @105
    @103
    @119
    vx
    @20
    @62
    @65
    @103
    @119
    wi
    #
    @71
    @64
    @63
    @120
    @2
    @64
    @103
    @43
    @119
    @107
    @42
    @118
    vy
    vz
    vy
    vz
    weq
    #
    @40
    @116
    @41
    @117
    @121
    @39
    @114
    @13
    @115
    @10
    @23
    @38
    psseq1
    @10
    @23
    treq
    anbi12d
    vy
    vz
    vu
    elequ1
    imbi12d
    cbvalv
    syl6ib
    3ad2ant3
    sylbi
    rexlimiv
    sylbi
    rgen
    vu
    vx
    vz
    @21
    dfon2lem6
    mp2an
    @102
    @90
    @112
    vx
    @102
    @88
    @110
    @89
    @111
    @102
    @87
    @109
    @2
    @38
    @21
    @0
    psseq2
    anbi1d
    @38
    @21
    @0
    eleq2
    imbi12d
    albidv
    mpbiri
    jaoi
    sylbi
    rgen
    @83
    @96
    @97
    w3a
    #
    @37
    @94
    wcel
    @98
    @93
    @122
    vs
    @37
    @21
    @77
    sucex
    @84
    @37
    wceq
    @85
    @83
    @86
    @96
    @92
    @97
    @84
    @37
    cA
    sseq1
    @84
    @37
    treq
    @91
    vu
    @84
    @37
    raleq
    3anbi123d
    elab
    @37
    @94
    elssuni
    sylbir
    mp3an23
    @94
    @46
    @93
    @45
    vs
    vw
    vs
    vw
    weq
    #
    @85
    @8
    @86
    @9
    @92
    @44
    @84
    @7
    cA
    sseq1
    @84
    @7
    treq
    @123
    @92
    @91
    vu
    @7
    wral
    @44
    @91
    vu
    @84
    @7
    raleq
    @91
    @43
    vu
    @7
    @90
    @42
    vx
    vy
    vx
    vy
    weq
    #
    @88
    @40
    @89
    @41
    @124
    @87
    @39
    @2
    @13
    @0
    @10
    @38
    psseq1
    @0
    @10
    treq
    anbi12d
    vx
    vy
    vu
    elequ1
    imbi12d
    cbvalv
    ralbii
    syl6bb
    3anbi123d
    cbvabv
    unieqi
    syl6sseq
    a1i
    syl5bir
    mpani
    syl5bi
    mtoi
    @6
    @35
    @99
    @36
    @100
    @5
    @35
    @99
    wa
    #
    @36
    wi
    vx
    @21
    @77
    @0
    @21
    wceq
    #
    @3
    @125
    @4
    @36
    @126
    @1
    @35
    @2
    @99
    @0
    @21
    cA
    psseq1
    @0
    @21
    treq
    anbi12d
    @0
    @21
    cA
    eleq1
    imbi12d
    spcv
    mpan2i
    mtod
    @81
    @22
    wn
    #
    @35
    @76
    @35
    @81
    @127
    wa
    @21
    cA
    dfpss2
    biimpri
    mpan
    nsyl2
    @22
    @28
    vz
    @21
    wral
    @29
    @28
    vz
    @21
    @23
    @21
    wcel
    vz
    vx
    wel
    #
    vx
    @20
    wrex
    @28
    vx
    @23
    @20
    eluni2
    @128
    @28
    vx
    @20
    @62
    @63
    @2
    @28
    vz
    @0
    wral
    #
    w3a
    #
    @128
    @28
    wi
    #
    @19
    @130
    vw
    @0
    @66
    @67
    @8
    @63
    @9
    @2
    @18
    @129
    @68
    @69
    @67
    @18
    @64
    @129
    @70
    @17
    @28
    vt
    vz
    @0
    @61
    @16
    @27
    vy
    @61
    @14
    @25
    @15
    @26
    @61
    @12
    @24
    @13
    @11
    @23
    @10
    psseq2
    anbi1d
    vt
    vz
    vy
    elequ2
    imbi12d
    albidv
    cbvralv
    syl6bb
    3anbi123d
    elab
    @129
    @63
    @131
    @2
    @28
    vz
    @0
    rsp
    3ad2ant3
    sylbi
    rexlimiv
    sylbi
    rgen
    @28
    vz
    @21
    cA
    raleq
    mpbii
    @28
    @34
    vz
    cB
    cA
    @23
    cB
    wceq
    #
    @27
    @33
    vy
    @132
    @25
    @31
    @26
    @32
    @132
    @24
    @30
    @13
    @23
    cB
    @10
    psseq2
    anbi1d
    @23
    cB
    @10
    eleq2
    imbi12d
    albidv
    rspccv
    3syl
end
