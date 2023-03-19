include "cupgr.mm"
include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "w3a.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cfv.mm"
include "cdm.mm"
include "crab.mm"
include "chash.mm"
include "csu.mm"
include "wceq.mm"
include "caddc.mm"
include "co.mm"
include "ciun.mm"
include "cun.mm"
include "diffi.mm"
include "adantr.mm"
include "3ad2ant2.mm"
include "dmfi.mm"
include "rabfi.mm"
include "syl.mm"
include "adantl.mm"
include "weq.mm"
include "cin.mm"
include "c0.mm"
include "wo.mm"
include "wral.mm"
include "wdisj.mm"
include "wn.mm"
include "notnotb.mm"
include "wi.mm"
include "cpr.mm"
include "wrex.mm"
include "cedg.mm"
include "wfun.mm"
include "cuhgr.mm"
include "upgruhgr.mm"
include "uhgrfun.mm"
include "iedgedg.mm"
include "sylan.mm"
include "eqid.mm"
include "upgredg.mm"
include "syldan.mm"
include "ex.mm"
include "3ad2ant1.mm"
include "imp.mm"
include "wne.mm"
include "eldifsni.mm"
include "3elpr2eq.mm"
include "expcom.mm"
include "3expd.mm"
include "com23.mm"
include "3imp.mm"
include "con3d.mm"
include "3exp.mm"
include "com24.mm"
include "eleq2.mm"
include "notbid.mm"
include "imbi12d.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "syl2an.mm"
include "mpd.mm"
include "syl5bir.mm"
include "orrd.mm"
include "anandi.mm"
include "bicomi.mm"
include "notbii.mm"
include "ianor.mm"
include "orbi2i.mm"
include "3bitri.mm"
include "sylibr.mm"
include "ralrimiva.mm"
include "inrab.mm"
include "eqeq1i.mm"
include "rabeq0.mm"
include "bitri.mm"
include "ralrimivva.mm"
include "eleq1w.mm"
include "anbi2d.mm"
include "rabbidv.mm"
include "disjor.mm"
include "hashiun.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "iunfi.mm"
include "syl2anc.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "eldifn.mm"
include "syl5ibr.mm"
include "intnand.mm"
include "eliun.mm"
include "ralnex.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "ralbii.mm"
include "3bitr2i.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "disjr.mm"
include "hashun.mm"
include "syl3anc.mm"
include "edglnl.mm"
include "3adant2.mm"
include "fveq2d.mm"
include "3eqtr2d.mm"

theorem numedglnl
  let vv: setvar v
  let vi: setvar i
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let vm: setvar m
  let vn: setvar n
  let vw: setvar w
  let vj: setvar j
  assume edglnl.v: |- V = ( Vtx ` G )
  assume edglnl.e: |- E = ( iEdg ` G )

  disjoint E v
  disjoint G i
  disjoint N i
  disjoint N v
  disjoint i v
  disjoint V i
  disjoint V v
  disjoint E i
  disjoint G v
  disjoint E m
  disjoint E n
  disjoint m n
  disjoint m v
  disjoint n v
  disjoint G m
  disjoint G n
  disjoint i m
  disjoint i n
  disjoint N m
  disjoint N n
  disjoint V m
  disjoint V n
  disjoint E w
  disjoint i w
  disjoint E j
  disjoint G j
  disjoint G w
  disjoint v w
  disjoint N j
  disjoint i j
  disjoint j v
  disjoint N w
  disjoint V j
  disjoint V w
  disjoint n w
  disjoint m w
  assert |- ( ( G e. UPGraph /\ ( V e. Fin /\ E e. Fin ) /\ N e. V ) -> ( sum_ v e. ( V \ { N } ) ( # ` { i e. dom E | ( N e. ( E ` i ) /\ v e. ( E ` i ) ) } ) + ( # ` { i e. dom E | ( E ` i ) = { N } } ) ) = ( # ` { i e. dom E | N e. ( E ` i ) } ) )

  proof
    cG
    cupgr
    wcel
    #
    cV
    cfn
    wcel
    #
    cE
    cfn
    wcel
    #
    wa
    #
    cN
    cV
    wcel
    #
    w3a
    #
    cV
    cN
    csn
    #
    cdif
    #
    cN
    vi
    cv
    #
    cE
    cfv
    #
    wcel
    #
    vv
    cv
    #
    @9
    wcel
    #
    wa
    #
    vi
    cE
    cdm
    #
    crab
    #
    chash
    cfv
    vv
    csu
    #
    @9
    @6
    wceq
    #
    vi
    @14
    crab
    #
    chash
    cfv
    #
    caddc
    co
    vv
    @7
    @15
    ciun
    #
    chash
    cfv
    #
    @19
    caddc
    co
    #
    @20
    @18
    cun
    #
    chash
    cfv
    #
    @10
    vi
    @14
    crab
    #
    chash
    cfv
    @5
    @16
    @21
    @19
    caddc
    @5
    @21
    @16
    @5
    vv
    @7
    @15
    @3
    @0
    @7
    cfn
    wcel
    #
    @4
    @1
    @26
    @2
    cV
    @6
    diffi
    adantr
    3ad2ant2
    #
    @5
    @15
    cfn
    wcel
    #
    @11
    @7
    wcel
    #
    @3
    @0
    @28
    @4
    @2
    @28
    @1
    @2
    @14
    cfn
    wcel
    #
    @28
    cE
    dmfi
    #
    @13
    vi
    @14
    rabfi
    syl
    adantl
    3ad2ant2
    adantr
    #
    @5
    vv
    vw
    weq
    #
    @15
    @10
    vw
    cv
    #
    @9
    wcel
    #
    wa
    #
    vi
    @14
    crab
    #
    cin
    #
    c0
    wceq
    #
    wo
    #
    vw
    @7
    wral
    vv
    @7
    wral
    vv
    @7
    @15
    wdisj
    @5
    @40
    vv
    vw
    @7
    @7
    @5
    @29
    @34
    @7
    wcel
    #
    wa
    #
    wa
    #
    @33
    @39
    @43
    @33
    wn
    #
    @39
    @43
    @44
    wa
    #
    @13
    @36
    wa
    #
    wn
    #
    vi
    @14
    wral
    #
    @39
    @45
    @47
    vi
    @14
    @45
    @8
    @14
    wcel
    #
    wa
    #
    @10
    wn
    #
    @12
    wn
    #
    @35
    wn
    #
    wo
    #
    wo
    #
    @47
    @50
    @51
    @54
    @51
    wn
    @10
    @50
    @54
    @10
    notnotb
    @50
    @10
    @54
    @50
    @10
    wa
    #
    @52
    @53
    @52
    wn
    @12
    @56
    @53
    @12
    notnotb
    @50
    @10
    @12
    @53
    wi
    #
    @50
    @9
    vm
    cv
    #
    vn
    cv
    #
    cpr
    #
    wceq
    #
    vn
    cV
    wrex
    vm
    cV
    wrex
    #
    @10
    @57
    wi
    #
    @45
    @49
    @62
    @43
    @49
    @62
    wi
    #
    @44
    @5
    @64
    @42
    @0
    @3
    @64
    @4
    @0
    @49
    @62
    @0
    @49
    @9
    cG
    cedg
    cfv
    #
    wcel
    #
    @62
    @0
    cE
    wfun
    #
    @49
    @66
    @0
    cG
    cuhgr
    wcel
    @67
    cG
    upgruhgr
    cE
    cG
    edglnl.e
    uhgrfun
    syl
    cE
    cG
    @8
    edglnl.e
    iedgedg
    sylan
    @9
    @65
    cG
    cV
    vm
    vn
    edglnl.v
    @65
    eqid
    upgredg
    syldan
    ex
    3ad2ant1
    adantr
    adantr
    imp
    @45
    @62
    @63
    wi
    #
    @49
    @43
    @44
    @68
    @42
    @44
    @68
    wi
    #
    @5
    @29
    @11
    cN
    wne
    #
    @34
    cN
    wne
    #
    @69
    @41
    @11
    cV
    cN
    eldifsni
    @34
    cV
    cN
    eldifsni
    @70
    @71
    wa
    #
    @44
    @68
    @72
    @44
    wa
    #
    @61
    @63
    vm
    vn
    cV
    cV
    @73
    @61
    @63
    wi
    @58
    cV
    wcel
    @59
    cV
    wcel
    wa
    @73
    @63
    @61
    cN
    @60
    wcel
    #
    @11
    @60
    wcel
    #
    @34
    @60
    wcel
    #
    wn
    #
    wi
    #
    wi
    #
    @72
    @44
    @79
    @72
    @75
    @74
    @44
    @77
    @72
    @75
    @74
    @44
    @77
    wi
    @72
    @75
    @74
    w3a
    @76
    @33
    @72
    @75
    @74
    @76
    @33
    wi
    #
    @72
    @74
    @75
    @80
    @72
    @74
    @75
    @76
    @33
    @74
    @75
    @76
    w3a
    @72
    @33
    @58
    @59
    cN
    @11
    @34
    3elpr2eq
    expcom
    3expd
    com23
    3imp
    con3d
    3exp
    com24
    imp
    @61
    @10
    @74
    @57
    @78
    @9
    @60
    cN
    eleq2
    @61
    @12
    @75
    @53
    @77
    @9
    @60
    @11
    eleq2
    @61
    @35
    @76
    @9
    @60
    @34
    eleq2
    notbid
    imbi12d
    imbi12d
    syl5ibrcom
    adantr
    rexlimdvva
    ex
    syl2an
    adantl
    imp
    adantr
    mpd
    imp
    syl5bir
    orrd
    ex
    syl5bir
    orrd
    @47
    @10
    @12
    @35
    wa
    #
    wa
    #
    wn
    @51
    @81
    wn
    #
    wo
    @55
    @46
    @82
    @82
    @46
    @10
    @12
    @35
    anandi
    bicomi
    notbii
    @10
    @81
    ianor
    @83
    @54
    @51
    @12
    @35
    ianor
    orbi2i
    3bitri
    sylibr
    ralrimiva
    @39
    @46
    vi
    @14
    crab
    #
    c0
    wceq
    @48
    @38
    @84
    c0
    @13
    @36
    vi
    @14
    inrab
    eqeq1i
    @46
    vi
    @14
    rabeq0
    bitri
    sylibr
    ex
    orrd
    ralrimivva
    @7
    @15
    @37
    vv
    vw
    @33
    @13
    @36
    vi
    @14
    @33
    @12
    @35
    @10
    vv
    vw
    @9
    eleq1w
    anbi2d
    rabbidv
    disjor
    sylibr
    hashiun
    eqcomd
    oveq1d
    @5
    @20
    cfn
    wcel
    #
    @18
    cfn
    wcel
    #
    @20
    @18
    cin
    c0
    wceq
    #
    @24
    @22
    wceq
    @5
    @26
    @28
    vv
    @7
    wral
    @85
    @27
    @5
    @28
    vv
    @7
    @32
    ralrimiva
    vv
    @7
    @15
    iunfi
    syl2anc
    @3
    @0
    @86
    @4
    @2
    @86
    @1
    @2
    @30
    @86
    @31
    @17
    vi
    @14
    rabfi
    syl
    adantl
    3ad2ant2
    @5
    vj
    cv
    #
    @20
    wcel
    #
    wn
    #
    vj
    @18
    wral
    @87
    @5
    @90
    vj
    @18
    @88
    @18
    wcel
    @88
    @14
    wcel
    #
    @88
    cE
    cfv
    #
    @6
    wceq
    #
    wa
    #
    @5
    @90
    @17
    @93
    vi
    @88
    @14
    vi
    vj
    weq
    #
    @9
    @92
    @6
    @8
    @88
    cE
    fveq2
    #
    eqeq1d
    elrab
    @5
    @94
    @90
    @5
    @94
    wa
    #
    @91
    cN
    @92
    wcel
    #
    @11
    @92
    wcel
    #
    wa
    #
    wa
    #
    wn
    #
    vv
    @7
    wral
    #
    @90
    @97
    @102
    vv
    @7
    @97
    @29
    wa
    #
    @100
    @91
    @104
    @99
    @98
    @97
    @29
    @99
    wn
    #
    @94
    @29
    @105
    wi
    #
    @5
    @93
    @106
    @91
    @29
    @105
    @93
    @11
    @6
    wcel
    #
    wn
    @11
    cV
    @6
    eldifn
    @93
    @99
    @107
    @92
    @6
    @11
    eleq2
    notbid
    syl5ibr
    adantl
    adantl
    imp
    intnand
    intnand
    ralrimiva
    @90
    @88
    @15
    wcel
    #
    vv
    @7
    wrex
    #
    wn
    @108
    wn
    #
    vv
    @7
    wral
    @103
    @89
    @109
    vv
    @88
    @7
    @15
    eliun
    notbii
    @108
    vv
    @7
    ralnex
    @110
    @102
    vv
    @7
    @108
    @101
    @13
    @100
    vi
    @88
    @14
    @95
    @10
    @98
    @12
    @99
    @95
    @9
    @92
    cN
    @96
    eleq2d
    @95
    @9
    @92
    @11
    @96
    eleq2d
    anbi12d
    elrab
    notbii
    ralbii
    3bitr2i
    sylibr
    ex
    syl5bi
    ralrimiv
    vj
    @20
    @18
    disjr
    sylibr
    @20
    @18
    hashun
    syl3anc
    @5
    @23
    @25
    chash
    @0
    @4
    @23
    @25
    wceq
    @3
    vv
    vi
    cE
    cG
    cN
    cV
    edglnl.v
    edglnl.e
    edglnl
    3adant2
    fveq2d
    3eqtr2d
end
