include "ccycls.mm"
include "cfv.mm"
include "wbr.mm"
include "cupgr.mm"
include "wcel.mm"
include "chash.mm"
include "c3.mm"
include "wceq.mm"
include "cv.mm"
include "cpr.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "wrex.mm"
include "cpths.mm"
include "cc0.mm"
include "wi.mm"
include "cyclprop.mm"
include "cwlks.mm"
include "pthiswlk.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfzo.mm"
include "wral.mm"
include "upgrwlkvtxedg.mm"
include "c2.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "ctp.mm"
include "oveq2.mm"
include "fzo0to3tp.mm"
include "syl6eq.mm"
include "raleqdv.mm"
include "c0ex.mm"
include "1ex.mm"
include "2ex.mm"
include "oveq1.mm"
include "0p1e1.mm"
include "fveq2d.mm"
include "preq12d.mm"
include "eleq1d.mm"
include "1p1e2.mm"
include "2p1e3.mm"
include "raltp.mm"
include "syl6bb.mm"
include "anbi12d.mm"
include "cfz.mm"
include "wf.mm"
include "wlkp.mm"
include "feq2d.mm"
include "id.mm"
include "cn0.mm"
include "3nn0.mm"
include "0elfz.mm"
include "mp1i.mm"
include "ffvelrnd.mm"
include "clt.mm"
include "1nn0.mm"
include "1lt3.mm"
include "fvffz0.mm"
include "ex.mm"
include "mp3an.mm"
include "2nn0.mm"
include "2lt3.mm"
include "3jca.mm"
include "syl6bi.mm"
include "com12.mm"
include "3syl.mm"
include "adantr.mm"
include "impcom.mm"
include "preq2.mm"
include "eqcoms.mm"
include "adantl.mm"
include "3anbi3d.mm"
include "biimpa.mm"
include "simpll.mm"
include "breq2.mm"
include "mpbiri.mm"
include "cn.mm"
include "3nn.mm"
include "lbfzo0.mm"
include "mpbir.mm"
include "syl5eleqr.mm"
include "pthdadjvtx.mm"
include "1e0p1.mm"
include "fveq2i.mm"
include "neeq2i.mm"
include "sylibr.mm"
include "syl3anc.mm"
include "elfzo0.mm"
include "mpbir3an.mm"
include "df-2.mm"
include "wb.mm"
include "neeq2.mm"
include "df-3.mm"
include "mpbird.mm"
include "preq1.mm"
include "3anbi13d.mm"
include "neeq1.mm"
include "3anbi12d.mm"
include "3anbi23d.mm"
include "rspc3ev.mm"
include "syl12anc.mm"
include "sylbid.mm"
include "expd.mm"
include "com13.mm"
include "syl.mm"
include "expcom.mm"
include "com23.mm"
include "mpcom.mm"
include "imp.mm"
include "3imp21.mm"

theorem upgr3v3e3cycl
  let cP: class P
  let cE: class E
  let cF: class F
  let cG: class G
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vk: setvar k
  assume upgr3v3e3cycl.e: |- E = ( Edg ` G )
  assume upgr3v3e3cycl.v: |- V = ( Vtx ` G )

  disjoint E a
  disjoint E b
  disjoint E c
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint E k
  disjoint F k
  disjoint G k
  disjoint P k
  assert |- ( ( G e. UPGraph /\ F ( Cycles ` G ) P /\ ( # ` F ) = 3 ) -> E. a e. V E. b e. V E. c e. V ( ( { a , b } e. E /\ { b , c } e. E /\ { c , a } e. E ) /\ ( a =/= b /\ b =/= c /\ c =/= a ) ) )

  proof
    cF
    cP
    cG
    ccycls
    cfv
    wbr
    #
    cG
    cupgr
    wcel
    #
    cF
    chash
    cfv
    #
    c3
    wceq
    #
    va
    cv
    #
    vb
    cv
    #
    cpr
    #
    cE
    wcel
    #
    @5
    vc
    cv
    #
    cpr
    #
    cE
    wcel
    #
    @8
    @4
    cpr
    #
    cE
    wcel
    #
    w3a
    #
    @4
    @5
    wne
    #
    @5
    @8
    wne
    #
    @8
    @4
    wne
    #
    w3a
    #
    wa
    #
    vc
    cV
    wrex
    vb
    cV
    wrex
    va
    cV
    wrex
    #
    @0
    cF
    cP
    cG
    cpths
    cfv
    wbr
    #
    cc0
    cP
    cfv
    #
    @2
    cP
    cfv
    #
    wceq
    #
    wa
    #
    @1
    @3
    @19
    wi
    #
    wi
    #
    cP
    cF
    cG
    cyclprop
    @20
    @23
    @26
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    @20
    @23
    @26
    wi
    cP
    cF
    cG
    pthiswlk
    #
    @27
    @20
    @23
    @26
    @27
    @1
    @24
    @25
    @1
    @27
    @24
    @25
    wi
    #
    @1
    @27
    wa
    vk
    cv
    #
    cP
    cfv
    #
    @30
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    vk
    cc0
    @2
    cfzo
    co
    #
    wral
    #
    @29
    cP
    vk
    cE
    cF
    cG
    upgr3v3e3cycl.e
    upgrwlkvtxedg
    @3
    @24
    @37
    @19
    @3
    @24
    @37
    @19
    @3
    @24
    @37
    wa
    @20
    @21
    c3
    cP
    cfv
    #
    wceq
    #
    wa
    #
    @21
    c1
    cP
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    @41
    c2
    cP
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    @44
    @38
    cpr
    #
    cE
    wcel
    #
    w3a
    #
    wa
    #
    @19
    @3
    @24
    @40
    @37
    @49
    @3
    @23
    @39
    @20
    @3
    @22
    @38
    @21
    @2
    c3
    cP
    fveq2
    eqeq2d
    anbi2d
    @3
    @37
    @35
    vk
    cc0
    c1
    c2
    ctp
    #
    wral
    @49
    @3
    @35
    vk
    @36
    @51
    @3
    @36
    cc0
    c3
    cfzo
    co
    #
    @51
    @2
    c3
    cc0
    cfzo
    oveq2
    #
    fzo0to3tp
    syl6eq
    raleqdv
    @35
    @43
    @46
    @48
    vk
    cc0
    c1
    c2
    c0ex
    1ex
    2ex
    @30
    cc0
    wceq
    #
    @34
    @42
    cE
    @54
    @31
    @21
    @33
    @41
    @30
    cc0
    cP
    fveq2
    @54
    @32
    c1
    cP
    @54
    @32
    cc0
    c1
    caddc
    co
    #
    c1
    @30
    cc0
    c1
    caddc
    oveq1
    0p1e1
    syl6eq
    fveq2d
    preq12d
    eleq1d
    @30
    c1
    wceq
    #
    @34
    @45
    cE
    @56
    @31
    @41
    @33
    @44
    @30
    c1
    cP
    fveq2
    @56
    @32
    c2
    cP
    @56
    @32
    c1
    c1
    caddc
    co
    #
    c2
    @30
    c1
    c1
    caddc
    oveq1
    1p1e2
    syl6eq
    fveq2d
    preq12d
    eleq1d
    @30
    c2
    wceq
    #
    @34
    @47
    cE
    @58
    @31
    @44
    @33
    @38
    @30
    c2
    cP
    fveq2
    @58
    @32
    c3
    cP
    @58
    @32
    c2
    c1
    caddc
    co
    #
    c3
    @30
    c2
    c1
    caddc
    oveq1
    2p1e3
    syl6eq
    fveq2d
    preq12d
    eleq1d
    raltp
    syl6bb
    anbi12d
    @3
    @50
    @19
    @3
    @50
    wa
    @21
    cV
    wcel
    #
    @41
    cV
    wcel
    #
    @44
    cV
    wcel
    #
    w3a
    #
    @43
    @46
    @44
    @21
    cpr
    #
    cE
    wcel
    #
    w3a
    #
    @21
    @41
    wne
    #
    @41
    @44
    wne
    #
    @44
    @21
    wne
    #
    w3a
    #
    @19
    @50
    @3
    @63
    @40
    @3
    @63
    wi
    #
    @49
    @20
    @71
    @39
    @20
    @27
    cc0
    @2
    cfz
    co
    #
    cV
    cP
    wf
    #
    @71
    @28
    cP
    cF
    cG
    cV
    upgr3v3e3cycl.v
    wlkp
    @3
    @73
    @63
    @3
    @73
    cc0
    c3
    cfz
    co
    #
    cV
    cP
    wf
    #
    @63
    @3
    @72
    @74
    cV
    cP
    @2
    c3
    cc0
    cfz
    oveq2
    feq2d
    @75
    @60
    @61
    @62
    @75
    @74
    cV
    cc0
    cP
    @75
    id
    c3
    cn0
    wcel
    #
    cc0
    @74
    wcel
    @75
    3nn0
    c3
    0elfz
    mp1i
    ffvelrnd
    @76
    c1
    cn0
    wcel
    #
    c1
    c3
    clt
    wbr
    #
    @75
    @61
    wi
    3nn0
    1nn0
    1lt3
    @76
    @77
    @78
    w3a
    @75
    @61
    cP
    c1
    c3
    cV
    fvffz0
    ex
    mp3an
    @76
    c2
    cn0
    wcel
    #
    c2
    c3
    clt
    wbr
    #
    @75
    @62
    wi
    3nn0
    2nn0
    2lt3
    @76
    @79
    @80
    w3a
    @75
    @62
    cP
    c2
    c3
    cV
    fvffz0
    ex
    mp3an
    3jca
    syl6bi
    com12
    3syl
    adantr
    adantr
    impcom
    @50
    @66
    @3
    @40
    @49
    @66
    @40
    @48
    @65
    @43
    @46
    @40
    @47
    @64
    cE
    @39
    @47
    @64
    wceq
    #
    @20
    @81
    @38
    @21
    @38
    @21
    @44
    preq2
    eqcoms
    adantl
    eleq1d
    3anbi3d
    biimpa
    adantl
    @50
    @3
    @70
    @40
    @3
    @70
    wi
    @49
    @40
    @3
    @70
    @40
    @3
    wa
    #
    @67
    @68
    @69
    @82
    @20
    c1
    @2
    clt
    wbr
    #
    cc0
    @36
    wcel
    #
    @67
    @20
    @39
    @3
    simpll
    #
    @3
    @83
    @40
    @3
    @83
    @78
    1lt3
    @2
    c3
    c1
    clt
    breq2
    mpbiri
    adantl
    #
    @3
    @84
    @40
    @3
    cc0
    @52
    @36
    cc0
    @52
    wcel
    c3
    cn
    wcel
    #
    3nn
    c3
    lbfzo0
    mpbir
    @53
    syl5eleqr
    adantl
    @20
    @83
    @84
    w3a
    @21
    @55
    cP
    cfv
    #
    wne
    @67
    cP
    cF
    cG
    cc0
    pthdadjvtx
    @41
    @88
    @21
    c1
    @55
    cP
    1e0p1
    fveq2i
    neeq2i
    sylibr
    syl3anc
    @82
    @20
    @83
    c1
    @36
    wcel
    #
    @68
    @85
    @86
    @3
    @89
    @40
    @3
    c1
    @52
    @36
    c1
    @52
    wcel
    @77
    @87
    @78
    1nn0
    3nn
    1lt3
    c1
    c3
    elfzo0
    mpbir3an
    @53
    syl5eleqr
    adantl
    @20
    @83
    @89
    w3a
    @41
    @57
    cP
    cfv
    #
    wne
    @68
    cP
    cF
    cG
    c1
    pthdadjvtx
    @44
    @90
    @41
    c2
    @57
    cP
    df-2
    fveq2i
    neeq2i
    sylibr
    syl3anc
    @82
    @69
    @44
    @59
    cP
    cfv
    #
    wne
    #
    @82
    @20
    @83
    c2
    @36
    wcel
    #
    @92
    @85
    @86
    @3
    @93
    @40
    @3
    c2
    @52
    @36
    c2
    @52
    wcel
    @79
    @87
    @80
    2nn0
    3nn
    2lt3
    c2
    c3
    elfzo0
    mpbir3an
    @53
    syl5eleqr
    adantl
    cP
    cF
    cG
    c2
    pthdadjvtx
    syl3anc
    @40
    @69
    @92
    wb
    #
    @3
    @39
    @94
    @20
    @39
    @69
    @44
    @38
    wne
    @92
    @21
    @38
    @44
    neeq2
    @38
    @91
    @44
    c3
    @59
    cP
    df-3
    fveq2i
    neeq2i
    syl6bb
    adantl
    adantr
    mpbird
    3jca
    ex
    adantr
    impcom
    @18
    @66
    @70
    wa
    @21
    @5
    cpr
    #
    cE
    wcel
    #
    @10
    @8
    @21
    cpr
    #
    cE
    wcel
    #
    w3a
    #
    @21
    @5
    wne
    #
    @15
    @8
    @21
    wne
    #
    w3a
    #
    wa
    @43
    @41
    @8
    cpr
    #
    cE
    wcel
    #
    @98
    w3a
    #
    @67
    @41
    @8
    wne
    #
    @101
    w3a
    #
    wa
    va
    vb
    vc
    @21
    @41
    @44
    cV
    cV
    cV
    @4
    @21
    wceq
    #
    @13
    @99
    @17
    @102
    @108
    @7
    @96
    @12
    @98
    @10
    @108
    @6
    @95
    cE
    @4
    @21
    @5
    preq1
    eleq1d
    @108
    @11
    @97
    cE
    @4
    @21
    @8
    preq2
    eleq1d
    3anbi13d
    @108
    @14
    @100
    @16
    @101
    @15
    @4
    @21
    @5
    neeq1
    @4
    @21
    @8
    neeq2
    3anbi13d
    anbi12d
    @5
    @41
    wceq
    #
    @99
    @105
    @102
    @107
    @109
    @96
    @43
    @10
    @104
    @98
    @109
    @95
    @42
    cE
    @5
    @41
    @21
    preq2
    eleq1d
    @109
    @9
    @103
    cE
    @5
    @41
    @8
    preq1
    eleq1d
    3anbi12d
    @109
    @100
    @67
    @15
    @106
    @101
    @5
    @41
    @21
    neeq2
    @5
    @41
    @8
    neeq1
    3anbi12d
    anbi12d
    @8
    @44
    wceq
    #
    @105
    @66
    @107
    @70
    @110
    @104
    @46
    @98
    @65
    @43
    @110
    @103
    @45
    cE
    @8
    @44
    @41
    preq2
    eleq1d
    @110
    @97
    @64
    cE
    @8
    @44
    @21
    preq1
    eleq1d
    3anbi23d
    @110
    @106
    @68
    @101
    @69
    @67
    @8
    @44
    @41
    neeq2
    @8
    @44
    @21
    neeq1
    3anbi23d
    anbi12d
    rspc3ev
    syl12anc
    ex
    sylbid
    expd
    com13
    syl
    expcom
    com23
    expd
    mpcom
    imp
    syl
    3imp21
end
