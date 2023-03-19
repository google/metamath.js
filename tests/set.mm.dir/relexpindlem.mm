include "cv.mm"
include "cn0.mm"
include "wcel.mm"
include "crelexp.mm"
include "co.mm"
include "wbr.mm"
include "wi.mm"
include "wa.mm"
include "wal.mm"
include "simpr.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "breqd.mm"
include "imbi1d.mm"
include "albidv.mm"
include "imbi12d.mm"
include "weq.mm"
include "cid.mm"
include "cuni.mm"
include "cres.mm"
include "cvv.mm"
include "wrel.mm"
include "jca.mm"
include "adantr.mm"
include "relexp0.mm"
include "syl.mm"
include "w3a.mm"
include "wex.mm"
include "simpl.mm"
include "adantl.mm"
include "simprl.mm"
include "jccil.mm"
include "expcom.mm"
include "3imp1.mm"
include "wb.mm"
include "ad2antll.mm"
include "bicomd.mm"
include "anbi1.mm"
include "syl6bi.mm"
include "mpcom.mm"
include "3jca.mm"
include "anassrs.mm"
include "impbid.mm"
include "spcegv.mm"
include "syl2anc.mm"
include "cop.mm"
include "df-br.mm"
include "sylib.mm"
include "vex.mm"
include "opelres.mm"
include "simpll.mm"
include "sylibr.mm"
include "ideq.mm"
include "mpancom.mm"
include "breq1.mm"
include "eqeq2.mm"
include "3anbi1d.mm"
include "exbidv.mm"
include "anbi1d.mm"
include "anbi12d.mm"
include "mpbid.mm"
include "3imp.mm"
include "exlimiv.mm"
include "ad2antrl.mm"
include "breq.mm"
include "syl5ibr.mm"
include "alrimiv.mm"
include "breq2.mm"
include "cbvalv.mm"
include "bicomi.mm"
include "imbi2.mm"
include "ccom.mm"
include "simprrr.mm"
include "relexpsucl.mm"
include "syl3anc.mm"
include "brcog.mm"
include "sylancl.mm"
include "simprrl.mm"
include "mpd.mm"
include "id.mm"
include "sp.mm"
include "ax-mp.mm"
include "syl3c.mm"
include "impcom.mm"
include "exlimddv.mm"
include "nn0ind.mm"
include "19.21bi.mm"
include "ex.mm"

theorem relexpindlem
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wet: wff et
  let vx: setvar x
  let cR: class R
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let vl: setvar l
  let vk: setvar k
  assume relexpindlem.1: |- ( et -> Rel R )
  assume relexpindlem.2: |- ( et -> R e. _V )
  assume relexpindlem.3: |- ( et -> S e. _V )
  assume relexpindlem.4: |- ( i = S -> ( ph <-> ch ) )
  assume relexpindlem.5: |- ( i = x -> ( ph <-> ps ) )
  assume relexpindlem.6: |- ( i = j -> ( ph <-> th ) )
  assume relexpindlem.7: |- ( et -> ch )
  assume relexpindlem.8: |- ( et -> ( j R x -> ( th -> ps ) ) )

  disjoint i x
  disjoint n x
  disjoint i j
  disjoint R i
  disjoint R j
  disjoint R x
  disjoint S i
  disjoint S j
  disjoint S x
  disjoint et i
  disjoint et j
  disjoint j x
  disjoint j ph
  disjoint ph x
  disjoint i ps
  disjoint j ps
  disjoint ch i
  disjoint i th
  disjoint et x
  disjoint i l
  disjoint l x
  disjoint k n
  disjoint k x
  disjoint j l
  disjoint R l
  disjoint R k
  disjoint S l
  disjoint S k
  disjoint et l
  disjoint k l
  disjoint k ps
  disjoint l ps
  disjoint et k
  assert |- ( et -> ( n e. NN0 -> ( S ( R ^r n ) x -> ps ) ) )

  proof
    wet
    vn
    cv
    #
    cn0
    wcel
    #
    cS
    vx
    cv
    #
    cR
    @0
    crelexp
    co
    #
    wbr
    #
    wps
    wi
    #
    wet
    @1
    wa
    #
    @5
    vx
    @1
    @6
    @5
    vx
    wal
    #
    wet
    @1
    simpr
    wet
    vk
    cv
    #
    cn0
    wcel
    #
    wa
    #
    cS
    @2
    cR
    @8
    crelexp
    co
    #
    wbr
    #
    wps
    wi
    #
    vx
    wal
    #
    wi
    wet
    cc0
    cn0
    wcel
    #
    wa
    #
    cS
    @2
    cR
    cc0
    crelexp
    co
    #
    wbr
    #
    wps
    wi
    #
    vx
    wal
    #
    wi
    wet
    vl
    cv
    #
    cn0
    wcel
    #
    wa
    #
    cS
    @2
    cR
    @21
    crelexp
    co
    #
    wbr
    #
    wps
    wi
    #
    vx
    wal
    #
    wi
    #
    wet
    @21
    c1
    caddc
    co
    #
    cn0
    wcel
    #
    wa
    #
    cS
    @2
    cR
    @29
    crelexp
    co
    #
    wbr
    #
    wps
    wi
    #
    vx
    wal
    #
    wi
    #
    @6
    @7
    wi
    vk
    vl
    @0
    @8
    cc0
    wceq
    #
    @10
    @16
    @14
    @20
    @37
    @9
    @15
    wet
    @8
    cc0
    cn0
    eleq1
    anbi2d
    @37
    @13
    @19
    vx
    @37
    @12
    @18
    wps
    @37
    @11
    @17
    cS
    @2
    @8
    cc0
    cR
    crelexp
    oveq2
    breqd
    imbi1d
    albidv
    imbi12d
    vk
    vl
    weq
    #
    @10
    @23
    @14
    @27
    @38
    @9
    @22
    wet
    @8
    @21
    cn0
    eleq1
    anbi2d
    @38
    @13
    @26
    vx
    @38
    @12
    @25
    wps
    @38
    @11
    @24
    cS
    @2
    @8
    @21
    cR
    crelexp
    oveq2
    breqd
    imbi1d
    albidv
    imbi12d
    @8
    @29
    wceq
    #
    @10
    @31
    @14
    @35
    @39
    @9
    @30
    wet
    @8
    @29
    cn0
    eleq1
    anbi2d
    @39
    @13
    @34
    vx
    @39
    @12
    @33
    wps
    @39
    @11
    @32
    cS
    @2
    @8
    @29
    cR
    crelexp
    oveq2
    breqd
    imbi1d
    albidv
    imbi12d
    vk
    vn
    weq
    #
    @10
    @6
    @14
    @7
    @40
    @9
    @1
    wet
    @8
    @0
    cn0
    eleq1
    anbi2d
    @40
    @13
    @5
    vx
    @40
    @12
    @4
    wps
    @40
    @11
    @3
    cS
    @2
    @8
    @0
    cR
    crelexp
    oveq2
    breqd
    imbi1d
    albidv
    imbi12d
    @16
    @19
    vx
    @17
    cid
    cR
    cuni
    cuni
    #
    cres
    #
    wceq
    #
    @16
    @19
    @16
    cR
    cvv
    wcel
    #
    cR
    wrel
    #
    wa
    #
    @43
    wet
    @46
    @15
    wet
    @44
    @45
    relexpindlem.2
    relexpindlem.1
    jca
    adantr
    cR
    cvv
    relexp0
    syl
    @16
    @19
    @43
    cS
    @2
    @42
    wbr
    #
    wps
    wi
    #
    vi
    cv
    #
    cS
    wceq
    #
    wph
    wet
    w3a
    #
    vi
    wex
    #
    @16
    @48
    @16
    wch
    wet
    @52
    wet
    wch
    @15
    relexpindlem.7
    adantr
    wet
    @15
    simpl
    cS
    cvv
    wcel
    #
    wch
    wet
    wa
    #
    @52
    wet
    @53
    wch
    relexpindlem.3
    adantl
    @51
    @54
    vi
    cS
    cvv
    @50
    @51
    @54
    @51
    @50
    @54
    @50
    wph
    wet
    @50
    @54
    wph
    @50
    wet
    @50
    @54
    wi
    #
    wi
    wet
    wph
    @50
    wa
    #
    @55
    @50
    wet
    @56
    wa
    #
    @54
    @50
    @57
    wa
    wet
    wch
    @50
    wet
    @56
    simprl
    relexpindlem.7
    jccil
    expcom
    expcom
    expcom
    3imp1
    expcom
    @54
    @50
    @51
    wch
    wet
    @50
    @51
    wch
    wet
    @50
    wa
    #
    wa
    #
    @50
    wph
    wet
    @58
    @50
    wch
    wet
    @50
    simpr
    adantl
    wch
    wph
    wb
    #
    @59
    wph
    @59
    wph
    wch
    @50
    wph
    wch
    wb
    wch
    wet
    relexpindlem.4
    ad2antll
    bicomd
    @60
    @59
    wph
    @58
    wa
    wph
    wch
    wph
    @58
    anbi1
    wph
    @58
    simpl
    syl6bi
    mpcom
    wch
    wet
    @50
    simprl
    3jca
    anassrs
    expcom
    impbid
    spcegv
    mpcom
    syl2anc
    @47
    @52
    @16
    wa
    #
    wps
    cS
    @2
    wceq
    #
    @47
    @61
    wa
    #
    wps
    cS
    @2
    cop
    #
    cid
    wcel
    #
    cS
    @41
    wcel
    #
    wa
    #
    @63
    @62
    @63
    @64
    @42
    wcel
    #
    @67
    @63
    @47
    @68
    @47
    @61
    simpl
    cS
    @2
    @42
    df-br
    sylib
    cS
    @2
    cid
    @41
    vx
    vex
    #
    opelres
    sylib
    @67
    @63
    wa
    #
    cS
    @2
    cid
    wbr
    #
    @62
    @70
    @65
    @71
    @65
    @66
    @63
    simpll
    cS
    @2
    cid
    df-br
    sylibr
    cS
    @2
    @69
    ideq
    sylib
    mpancom
    @62
    @63
    @2
    @2
    @42
    wbr
    #
    vi
    vx
    weq
    #
    wph
    wet
    w3a
    #
    vi
    wex
    #
    @16
    wa
    #
    wa
    wps
    @62
    @47
    @72
    @61
    @76
    cS
    @2
    @2
    @42
    breq1
    @62
    @52
    @75
    @16
    @62
    @51
    @74
    vi
    @62
    @50
    @73
    wph
    wet
    cS
    @2
    @49
    eqeq2
    3anbi1d
    exbidv
    anbi1d
    anbi12d
    @75
    wps
    @72
    @16
    @74
    wps
    vi
    @73
    wph
    wet
    wps
    wph
    @73
    wet
    wps
    wi
    wet
    wph
    @73
    wa
    #
    wps
    wet
    @77
    wa
    wph
    wps
    wet
    wph
    @73
    simprl
    @73
    wph
    wps
    wb
    wet
    wph
    relexpindlem.5
    ad2antll
    mpbid
    expcom
    expcom
    3imp
    exlimiv
    ad2antrl
    syl6bi
    mpcom
    expcom
    mpancom
    @43
    @18
    @47
    wps
    cS
    @2
    @17
    @42
    breq
    imbi1d
    syl5ibr
    mpcom
    alrimiv
    @28
    @22
    @36
    @31
    @28
    @22
    wa
    #
    @35
    wet
    @30
    @78
    @35
    @27
    cS
    @49
    @24
    wbr
    #
    wph
    wi
    #
    vi
    wal
    #
    wb
    #
    wet
    @30
    @78
    wa
    #
    wa
    #
    @35
    wi
    @81
    @27
    @80
    @26
    vi
    vx
    @73
    @79
    @25
    wph
    wps
    @49
    @2
    cS
    @24
    breq2
    relexpindlem.5
    imbi12d
    cbvalv
    bicomi
    @82
    @84
    wet
    @30
    @23
    @81
    wi
    #
    @22
    wa
    #
    wa
    #
    wa
    #
    @35
    @82
    @83
    @87
    wet
    @82
    @78
    @86
    @30
    @82
    @28
    @85
    @22
    @27
    @81
    @23
    imbi2
    anbi1d
    anbi2d
    anbi2d
    @88
    @34
    vx
    @32
    cR
    @24
    ccom
    #
    wceq
    #
    @88
    @34
    @88
    @44
    @45
    @22
    @90
    wet
    @44
    @87
    relexpindlem.2
    adantr
    wet
    @45
    @87
    relexpindlem.1
    adantr
    wet
    @30
    @85
    @22
    simprrr
    cR
    @21
    cvv
    relexpsucl
    syl3anc
    @88
    @34
    @90
    cS
    @2
    @89
    wbr
    #
    wps
    wi
    #
    @91
    @88
    wps
    @91
    @88
    wa
    #
    cS
    vj
    cv
    #
    @24
    wbr
    #
    @94
    @2
    cR
    wbr
    #
    wa
    #
    wps
    vj
    @93
    @91
    @97
    vj
    wex
    #
    @91
    @88
    simpl
    @93
    @53
    @2
    cvv
    wcel
    @91
    @98
    wb
    wet
    @53
    @91
    @87
    relexpindlem.3
    ad2antrl
    @69
    vj
    cS
    @2
    cR
    @24
    cvv
    cvv
    brcog
    sylancl
    mpbid
    @91
    @88
    @97
    wps
    @88
    @97
    wa
    @91
    wps
    wet
    @87
    @97
    @92
    @87
    @97
    wa
    wet
    @92
    @30
    @86
    @97
    wet
    @92
    wi
    #
    @86
    @97
    wa
    @30
    @99
    @85
    @22
    @97
    @30
    @99
    wi
    @30
    @85
    @22
    @97
    wa
    #
    wa
    #
    @99
    wet
    @30
    @101
    wa
    #
    @92
    @91
    wet
    @102
    wa
    #
    wps
    @81
    @91
    @103
    wa
    #
    wps
    @104
    @23
    @81
    @104
    wet
    @22
    @91
    wet
    @102
    simprl
    @102
    @22
    @91
    wet
    @30
    @85
    @22
    @97
    simprrl
    ad2antll
    jca
    @102
    @85
    @91
    wet
    @30
    @85
    @100
    simprl
    ad2antll
    mpd
    @81
    @104
    wa
    #
    wet
    @96
    wth
    wps
    @81
    @91
    wet
    @102
    simprrl
    @103
    @96
    @81
    @91
    @101
    @96
    wet
    @30
    @85
    @22
    @95
    @96
    simprrr
    ad2antll
    ad2antll
    @81
    @95
    wth
    wi
    #
    vj
    wal
    #
    wb
    #
    @105
    wth
    wi
    @80
    @106
    vi
    vj
    vi
    vj
    weq
    @79
    @95
    wph
    wth
    @49
    @94
    cS
    @24
    breq2
    relexpindlem.6
    imbi12d
    cbvalv
    @108
    @105
    @107
    @91
    wet
    @30
    @23
    @107
    wi
    #
    @100
    wa
    #
    wa
    #
    wa
    #
    wa
    #
    wa
    #
    wth
    @108
    @81
    @107
    @104
    @113
    @108
    id
    @108
    @103
    @112
    @91
    @108
    @102
    @111
    wet
    @108
    @101
    @110
    @30
    @108
    @85
    @109
    @100
    @81
    @107
    @23
    imbi2
    anbi1d
    anbi2d
    anbi2d
    anbi2d
    anbi12d
    @114
    @95
    wth
    @112
    @95
    @107
    @91
    @110
    @95
    wet
    @30
    @109
    @22
    @95
    @96
    simprrl
    ad2antll
    ad2antll
    @107
    @106
    @113
    @106
    vj
    sp
    adantr
    mpd
    syl6bi
    ax-mp
    relexpindlem.8
    syl3c
    mpancom
    expcom
    expcom
    expcom
    anassrs
    impcom
    anassrs
    impcom
    anassrs
    impcom
    anassrs
    exlimddv
    expcom
    @90
    @33
    @91
    wps
    cS
    @2
    @32
    @89
    breq
    imbi1d
    syl5ibr
    mpcom
    alrimiv
    syl6bi
    ax-mp
    anassrs
    expcom
    expcom
    nn0ind
    mpcom
    19.21bi
    ex
end
