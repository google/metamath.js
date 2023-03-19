include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "crn.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wfn.mm"
include "wb.mm"
include "crio.mm"
include "riotaex.mm"
include "fnmpti.mm"
include "fvelrnb.mm"
include "ax-mp.mm"
include "crab.mm"
include "weq.mm"
include "eqeq2.mm"
include "riotabidv.mm"
include "fvmpt.mm"
include "syl6eqr.mm"
include "adantl.mm"
include "eqeq1d.mm"
include "rexbidva.mm"
include "co.mm"
include "simpl1.mm"
include "simprl.mm"
include "simpl2l.mm"
include "ltrnat.mm"
include "syl3anc.mm"
include "cbs.mm"
include "eqid.mm"
include "clat.mm"
include "simpl1l.mm"
include "hllat.mm"
include "syl.mm"
include "atbase.mm"
include "ltrncl.mm"
include "latjcl.mm"
include "simpl3l.mm"
include "hlatjcl.mm"
include "latlej2.mm"
include "simpl2.mm"
include "trljat1.mm"
include "simprr.mm"
include "wi.mm"
include "trlcl.mm"
include "syl2anc.mm"
include "latjlej2.mm"
include "syl13anc.mm"
include "mpd.mm"
include "eqbrtrrd.mm"
include "lattrd.mm"
include "ltrnel.mm"
include "simprd.mm"
include "jca.mm"
include "breq1.mm"
include "notbid.mm"
include "anbi12d.mm"
include "elrab2.mm"
include "sylanbrc.mm"
include "cdlemeiota.mm"
include "eqcomd.mm"
include "syl5eq.mm"
include "rspcev.mm"
include "ex.mm"
include "simpl2r.mm"
include "simprrr.mm"
include "ltrniotacl.mm"
include "ltrniotaval.mm"
include "syl122anc.mm"
include "simp3l.mm"
include "cmee.mm"
include "simp11.mm"
include "simp12.mm"
include "trlval2.mm"
include "simp3r.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "hlatlej1.mm"
include "simprrl.mm"
include "ad2antrl.mm"
include "latjle12.mm"
include "mpbi2and.mm"
include "simpl1r.mm"
include "lhpbase.mm"
include "latmlem1.mm"
include "lhpat4N.mm"
include "adantr.mm"
include "breqtrd.mm"
include "3adant3.mm"
include "eqbrtrd.mm"
include "mpd3an3.mm"
include "sylan2b.mm"
include "eleq1.mm"
include "fveq2.mm"
include "breq1d.mm"
include "biimpcd.mm"
include "syl6.mm"
include "rexlimdv.mm"
include "impbid.mm"
include "bitr4d.mm"
include "elrab.mm"
include "syl6bbr.mm"
include "simp1l.mm"
include "simp1r.mm"
include "diaval.mm"
include "syl22anc.mm"
include "eleq2d.mm"
include "syl5bb.mm"
include "eqrdv.mm"

theorem cdlemm10N
  let cA: class A
  let cC: class C
  let cP: class P
  let cR: class R
  let cT: class T
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vr: setvar r
  let vq: setvar q
  let vg: setvar g
  assume cdlemm10.l: |- .<_ = ( le ` K )
  assume cdlemm10.j: |- .\/ = ( join ` K )
  assume cdlemm10.a: |- A = ( Atoms ` K )
  assume cdlemm10.h: |- H = ( LHyp ` K )
  assume cdlemm10.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemm10.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemm10.i: |- I = ( ( DIsoA ` K ) ` W )
  assume cdlemm10.c: |- C = { r e. A | ( r .<_ ( P .\/ V ) /\ -. r .<_ W ) }
  assume cdlemm10.f: |- F = ( iota_ f e. T ( f ` P ) = s )
  assume cdlemm10.g: |- G = ( q e. C |-> ( iota_ f e. T ( f ` P ) = q ) )

  disjoint f r
  disjoint f s
  disjoint .<_ f
  disjoint r s
  disjoint .<_ r
  disjoint .<_ s
  disjoint .\/ r
  disjoint A f
  disjoint A r
  disjoint A s
  disjoint q s
  disjoint C q
  disjoint C s
  disjoint G s
  disjoint H f
  disjoint H s
  disjoint K f
  disjoint K s
  disjoint f q
  disjoint P f
  disjoint q r
  disjoint P q
  disjoint P r
  disjoint P s
  disjoint R f
  disjoint R s
  disjoint T f
  disjoint T q
  disjoint T s
  disjoint V f
  disjoint V r
  disjoint V s
  disjoint W f
  disjoint W r
  disjoint W s
  disjoint f g
  disjoint g r
  disjoint g s
  disjoint .<_ g
  disjoint A g
  disjoint G g
  disjoint H g
  disjoint I g
  disjoint K g
  disjoint g q
  disjoint P g
  disjoint V g
  disjoint W g
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( V e. A /\ V .<_ W ) ) -> ran G = ( I ` V ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cV
    cA
    wcel
    #
    cV
    cW
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    vg
    cG
    crn
    #
    cV
    cI
    cfv
    #
    vg
    cv
    #
    @10
    wcel
    #
    vs
    cv
    #
    cG
    cfv
    #
    @12
    wceq
    #
    vs
    cC
    wrex
    #
    @9
    @12
    @11
    wcel
    #
    cG
    cC
    wfn
    @13
    @17
    wb
    vq
    cC
    cP
    vf
    cv
    #
    cfv
    #
    vq
    cv
    #
    wceq
    #
    vf
    cT
    crio
    #
    cG
    @22
    vf
    cT
    riotaex
    cdlemm10.g
    fnmpti
    vs
    cC
    @12
    cG
    fvelrnb
    ax-mp
    @9
    @17
    @12
    @19
    cR
    cfv
    #
    cV
    c.le
    wbr
    #
    vf
    cT
    crab
    #
    wcel
    #
    @18
    @9
    @17
    @12
    cT
    wcel
    #
    @12
    cR
    cfv
    #
    cV
    c.le
    wbr
    #
    wa
    #
    @27
    @9
    @17
    cF
    @12
    wceq
    #
    vs
    cC
    wrex
    #
    @31
    @9
    @16
    @32
    vs
    cC
    @9
    @14
    cC
    wcel
    #
    wa
    @15
    cF
    @12
    @34
    @15
    cF
    wceq
    @9
    @34
    @15
    @20
    @14
    wceq
    #
    vf
    cT
    crio
    #
    cF
    vq
    @14
    @23
    @36
    cC
    cG
    vq
    vs
    weq
    @22
    @35
    vf
    cT
    @21
    @14
    @20
    eqeq2
    riotabidv
    cdlemm10.g
    @35
    vf
    cT
    riotaex
    fvmpt
    cdlemm10.f
    syl6eqr
    adantl
    eqeq1d
    rexbidva
    @9
    @31
    @33
    @9
    @31
    @33
    @9
    @31
    wa
    #
    cP
    @12
    cfv
    #
    cC
    wcel
    #
    @20
    @38
    wceq
    #
    vf
    cT
    crio
    #
    @12
    wceq
    #
    @33
    @37
    @38
    cA
    wcel
    #
    @38
    cP
    cV
    c.or
    co
    #
    c.le
    wbr
    #
    @38
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    @39
    @37
    @2
    @28
    @3
    @43
    @2
    @5
    @8
    @31
    simpl1
    #
    @9
    @28
    @30
    simprl
    #
    @3
    @4
    @2
    @8
    @31
    simpl2l
    #
    cA
    cP
    cT
    @12
    cH
    cK
    c.le
    cW
    cdlemm10.l
    cdlemm10.a
    cdlemm10.h
    cdlemm10.t
    ltrnat
    syl3anc
    @37
    @45
    @47
    @37
    cK
    cbs
    cfv
    #
    cK
    c.le
    @38
    cP
    @38
    c.or
    co
    #
    @44
    @52
    eqid
    #
    cdlemm10.l
    @37
    @0
    cK
    clat
    wcel
    #
    @0
    @1
    @5
    @8
    @31
    simpl1l
    #
    cK
    hllat
    #
    syl
    #
    @37
    @2
    @28
    cP
    @52
    wcel
    #
    @38
    @52
    wcel
    #
    @49
    @50
    @37
    @3
    @59
    @51
    cA
    @52
    cP
    cK
    @54
    cdlemm10.a
    atbase
    #
    syl
    #
    @52
    cT
    @12
    cH
    cK
    chlt
    cW
    cP
    @54
    cdlemm10.h
    cdlemm10.t
    ltrncl
    syl3anc
    #
    @37
    @55
    @59
    @60
    @53
    @52
    wcel
    @58
    @62
    @63
    @52
    c.or
    cK
    cP
    @38
    @54
    cdlemm10.j
    latjcl
    syl3anc
    @37
    @0
    @3
    @6
    @44
    @52
    wcel
    #
    @56
    @51
    @6
    @7
    @2
    @5
    @31
    simpl3l
    #
    cA
    @52
    c.or
    cK
    cP
    cV
    @54
    cdlemm10.j
    cdlemm10.a
    hlatjcl
    #
    syl3anc
    @37
    @55
    @59
    @60
    @38
    @53
    c.le
    wbr
    @58
    @62
    @63
    @52
    c.or
    cK
    c.le
    cP
    @38
    @54
    cdlemm10.l
    cdlemm10.j
    latlej2
    syl3anc
    @37
    cP
    @29
    c.or
    co
    #
    @53
    @44
    c.le
    @37
    @2
    @28
    @5
    @67
    @53
    wceq
    @49
    @50
    @2
    @5
    @8
    @31
    simpl2
    #
    cA
    cP
    cR
    cT
    @12
    cH
    c.or
    cK
    c.le
    cW
    cdlemm10.l
    cdlemm10.j
    cdlemm10.a
    cdlemm10.h
    cdlemm10.t
    cdlemm10.r
    trljat1
    syl3anc
    @37
    @30
    @67
    @44
    c.le
    wbr
    #
    @9
    @28
    @30
    simprr
    @37
    @55
    @29
    @52
    wcel
    #
    cV
    @52
    wcel
    #
    @59
    @30
    @69
    wi
    @58
    @37
    @2
    @28
    @70
    @49
    @50
    @52
    cR
    cT
    @12
    cH
    cK
    cW
    @54
    cdlemm10.h
    cdlemm10.t
    cdlemm10.r
    trlcl
    syl2anc
    @37
    @6
    @71
    @65
    cA
    @52
    cV
    cK
    @54
    cdlemm10.a
    atbase
    #
    syl
    @62
    @52
    c.or
    cK
    c.le
    @29
    cV
    cP
    @54
    cdlemm10.l
    cdlemm10.j
    latjlej2
    syl13anc
    mpd
    eqbrtrrd
    lattrd
    @37
    @2
    @28
    @5
    @47
    @49
    @50
    @68
    @2
    @28
    @5
    w3a
    @43
    @47
    cA
    cP
    cT
    @12
    cH
    cK
    c.le
    cW
    cdlemm10.l
    cdlemm10.a
    cdlemm10.h
    cdlemm10.t
    ltrnel
    simprd
    syl3anc
    jca
    vr
    cv
    #
    @44
    c.le
    wbr
    #
    @73
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    @48
    vr
    @38
    cA
    cC
    @73
    @38
    wceq
    #
    @74
    @45
    @76
    @47
    @73
    @38
    @44
    c.le
    breq1
    @78
    @75
    @46
    @73
    @38
    cW
    c.le
    breq1
    notbid
    anbi12d
    cdlemm10.c
    elrab2
    sylanbrc
    @37
    @12
    @41
    @37
    @2
    @5
    @28
    @12
    @41
    wceq
    @49
    @68
    @50
    cA
    cP
    cT
    vf
    @12
    cH
    cK
    c.le
    cW
    cdlemm10.l
    cdlemm10.a
    cdlemm10.h
    cdlemm10.t
    cdlemeiota
    syl3anc
    eqcomd
    @32
    @42
    vs
    @38
    cC
    @14
    @38
    wceq
    #
    cF
    @41
    @12
    @79
    cF
    @36
    @41
    cdlemm10.f
    @79
    @35
    @40
    vf
    cT
    @14
    @38
    @20
    eqeq2
    riotabidv
    syl5eq
    eqeq1d
    rspcev
    syl2anc
    ex
    @9
    @32
    @31
    vs
    cC
    @9
    @34
    cF
    cT
    wcel
    #
    cF
    cR
    cfv
    #
    cV
    c.le
    wbr
    #
    wa
    #
    @32
    @31
    wi
    @9
    @34
    @83
    @34
    @9
    @14
    cA
    wcel
    #
    @14
    @44
    c.le
    wbr
    #
    @14
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    wa
    #
    @83
    @77
    @88
    vr
    @14
    cA
    cC
    vr
    vs
    weq
    #
    @74
    @85
    @76
    @87
    @73
    @14
    @44
    c.le
    breq1
    @90
    @75
    @86
    @73
    @14
    cW
    c.le
    breq1
    notbid
    anbi12d
    cdlemm10.c
    elrab2
    @9
    @89
    @80
    cP
    cF
    cfv
    #
    @14
    wceq
    #
    wa
    #
    @83
    @9
    @89
    wa
    #
    @2
    @3
    @4
    @84
    @87
    @93
    @2
    @5
    @8
    @89
    simpl1
    @3
    @4
    @2
    @8
    @89
    simpl2l
    #
    @3
    @4
    @2
    @8
    @89
    simpl2r
    @9
    @84
    @88
    simprl
    #
    @9
    @84
    @85
    @87
    simprrr
    @2
    @5
    @84
    @87
    wa
    w3a
    @80
    @92
    cA
    cP
    @14
    cT
    vf
    cF
    cH
    cK
    c.le
    cW
    cdlemm10.l
    cdlemm10.a
    cdlemm10.h
    cdlemm10.t
    cdlemm10.f
    ltrniotacl
    cA
    cP
    @14
    cT
    vf
    cF
    cH
    cK
    c.le
    cW
    cdlemm10.l
    cdlemm10.a
    cdlemm10.h
    cdlemm10.t
    cdlemm10.f
    ltrniotaval
    jca
    syl122anc
    @9
    @89
    @93
    w3a
    #
    @80
    @82
    @9
    @89
    @80
    @92
    simp3l
    #
    @97
    @81
    cP
    @14
    c.or
    co
    #
    cW
    cK
    cmee
    cfv
    #
    co
    #
    cV
    c.le
    @97
    @81
    cP
    @91
    c.or
    co
    #
    cW
    @100
    co
    #
    @101
    @97
    @2
    @80
    @5
    @81
    @103
    wceq
    @2
    @5
    @8
    @89
    @93
    simp11
    @98
    @2
    @5
    @8
    @89
    @93
    simp12
    cA
    cP
    cR
    cT
    cF
    cH
    c.or
    cK
    c.le
    @100
    cW
    cdlemm10.l
    cdlemm10.j
    @100
    eqid
    #
    cdlemm10.a
    cdlemm10.h
    cdlemm10.t
    cdlemm10.r
    trlval2
    syl3anc
    @97
    @102
    @99
    cW
    @100
    @97
    @91
    @14
    cP
    c.or
    @9
    @89
    @80
    @92
    simp3r
    oveq2d
    oveq1d
    eqtrd
    @9
    @89
    @101
    cV
    c.le
    wbr
    @93
    @94
    @101
    @44
    cW
    @100
    co
    #
    cV
    c.le
    @94
    @99
    @44
    c.le
    wbr
    #
    @101
    @105
    c.le
    wbr
    #
    @94
    cP
    @44
    c.le
    wbr
    #
    @85
    @106
    @94
    @0
    @3
    @6
    @108
    @0
    @1
    @5
    @8
    @89
    simpl1l
    #
    @95
    @6
    @7
    @2
    @5
    @89
    simpl3l
    #
    cA
    cP
    cV
    c.or
    cK
    c.le
    cdlemm10.l
    cdlemm10.j
    cdlemm10.a
    hlatlej1
    syl3anc
    @9
    @84
    @85
    @87
    simprrl
    @94
    @55
    @59
    @14
    @52
    wcel
    #
    @64
    @108
    @85
    wa
    @106
    wb
    @94
    @0
    @55
    @109
    @57
    syl
    #
    @94
    @3
    @59
    @95
    @61
    syl
    @84
    @111
    @9
    @88
    cA
    @52
    @14
    cK
    @54
    cdlemm10.a
    atbase
    ad2antrl
    @94
    @0
    @3
    @6
    @64
    @109
    @95
    @110
    @66
    syl3anc
    #
    @52
    c.or
    cK
    c.le
    cP
    @14
    @44
    @54
    cdlemm10.l
    cdlemm10.j
    latjle12
    syl13anc
    mpbi2and
    @94
    @55
    @99
    @52
    wcel
    #
    @64
    cW
    @52
    wcel
    #
    @106
    @107
    wi
    @112
    @94
    @0
    @3
    @84
    @114
    @109
    @95
    @96
    cA
    @52
    c.or
    cK
    cP
    @14
    @54
    cdlemm10.j
    cdlemm10.a
    hlatjcl
    syl3anc
    @113
    @94
    @1
    @115
    @0
    @1
    @5
    @8
    @89
    simpl1r
    @52
    cH
    cK
    cW
    @54
    cdlemm10.h
    lhpbase
    syl
    @52
    cK
    c.le
    @100
    @99
    @44
    cW
    @54
    cdlemm10.l
    @104
    latmlem1
    syl13anc
    mpd
    @9
    @105
    cV
    wceq
    @89
    cA
    cP
    cV
    cH
    c.or
    cK
    c.le
    @100
    cW
    cdlemm10.l
    cdlemm10.j
    @104
    cdlemm10.a
    cdlemm10.h
    lhpat4N
    adantr
    breqtrd
    3adant3
    eqbrtrd
    jca
    mpd3an3
    sylan2b
    ex
    @32
    @83
    @31
    @32
    @80
    @28
    @82
    @30
    cF
    @12
    cT
    eleq1
    @32
    @81
    @29
    cV
    c.le
    cF
    @12
    cR
    fveq2
    breq1d
    anbi12d
    biimpcd
    syl6
    rexlimdv
    impbid
    bitr4d
    @25
    @30
    vf
    @12
    cT
    vf
    vg
    weq
    @24
    @29
    cV
    c.le
    @19
    @12
    cR
    fveq2
    breq1d
    elrab
    syl6bbr
    @9
    @11
    @26
    @12
    @9
    @0
    @1
    @71
    @7
    @11
    @26
    wceq
    @0
    @1
    @5
    @8
    simp1l
    @0
    @1
    @5
    @8
    simp1r
    @9
    @6
    @71
    @2
    @5
    @6
    @7
    simp3l
    @72
    syl
    @2
    @5
    @6
    @7
    simp3r
    @52
    cR
    cT
    vf
    cH
    cI
    cK
    c.le
    chlt
    cW
    cV
    @54
    cdlemm10.l
    cdlemm10.h
    cdlemm10.t
    cdlemm10.r
    cdlemm10.i
    diaval
    syl22anc
    eleq2d
    bitr4d
    syl5bb
    eqrdv
end
