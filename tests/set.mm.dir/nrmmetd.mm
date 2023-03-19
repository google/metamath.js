include "cxp.mm"
include "cr.mm"
include "ccom.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cgrp.mm"
include "grpsubf.mm"
include "syl.mm"
include "fco.mm"
include "syl2anc.mm"
include "cop.mm"
include "opelxpi.mm"
include "fvco3.mm"
include "syl2an.mm"
include "df-ov.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"
include "eqeq1d.mm"
include "grpsubcl.mm"
include "3expb.mm"
include "sylan.mm"
include "ralrimiva.mm"
include "fveq2.mm"
include "eqeq1.mm"
include "bibi12d.mm"
include "rspccva.mm"
include "syldan.mm"
include "grpsubeq0.mm"
include "3bitrd.mm"
include "adantr.mm"
include "adantrr.mm"
include "ffvelrnd.mm"
include "simprll.mm"
include "simprr.mm"
include "syl3anc.mm"
include "simprlr.mm"
include "readdcld.mm"
include "grpnnncan2.mm"
include "syl13anc.mm"
include "fveq2d.mm"
include "ralrimivva.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "eqbrtrrd.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "imbi12d.mm"
include "grpidcl.mm"
include "simprl.mm"
include "cminusg.mm"
include "eqid.mm"
include "grpinvval2.mm"
include "grpinvsub.mm"
include "eqtr3d.mm"
include "pm5.501.mm"
include "bicom.mm"
include "syl6bb.mm"
include "bitr3d.mm"
include "recnd.mm"
include "addid2d.mm"
include "eqtrd.mm"
include "3brtr3d.mm"
include "chvarv.mm"
include "adantrlr.mm"
include "anbi1d.mm"
include "adantrll.mm"
include "le2addd.mm"
include "letrd.mm"
include "oveq12d.mm"
include "3brtr4d.mm"
include "expr.mm"
include "ralrimiv.mm"
include "jca.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ismet.mm"
include "ax-mp.mm"
include "sylanbrc.mm"

theorem nrmmetd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume nrmmetd.x: |- X = ( Base ` G )
  assume nrmmetd.m: |- .- = ( -g ` G )
  assume nrmmetd.z: |- .0. = ( 0g ` G )
  assume nrmmetd.g: |- ( ph -> G e. Grp )
  assume nrmmetd.f: |- ( ph -> F : X --> RR )
  assume nrmmetd.1: |- ( ( ph /\ x e. X ) -> ( ( F ` x ) = 0 <-> x = .0. ) )
  assume nrmmetd.2: |- ( ( ph /\ ( x e. X /\ y e. X ) ) -> ( F ` ( x .- y ) ) <_ ( ( F ` x ) + ( F ` y ) ) )

  disjoint x y
  disjoint .- x
  disjoint .- y
  disjoint .0. x
  disjoint .0. y
  disjoint F x
  disjoint F y
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint .- a
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint .- b
  disjoint c x
  disjoint c y
  disjoint .- c
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint X a
  disjoint X b
  disjoint X c
  assert |- ( ph -> ( F o. .- ) e. ( Met ` X ) )

  proof
    wph
    cX
    cX
    cxp
    #
    cr
    cF
    c.mi
    ccom
    #
    wf
    #
    va
    cv
    #
    vb
    cv
    #
    @1
    co
    #
    cc0
    wceq
    #
    @3
    @4
    wceq
    #
    wb
    #
    @5
    vc
    cv
    #
    @3
    @1
    co
    #
    @9
    @4
    @1
    co
    #
    caddc
    co
    #
    cle
    wbr
    #
    vc
    cX
    wral
    #
    wa
    #
    vb
    cX
    wral
    va
    cX
    wral
    #
    @1
    cX
    cme
    cfv
    wcel
    #
    wph
    cX
    cr
    cF
    wf
    #
    @0
    cX
    c.mi
    wf
    #
    @2
    nrmmetd.f
    wph
    cG
    cgrp
    wcel
    #
    @19
    nrmmetd.g
    cX
    cG
    c.mi
    nrmmetd.x
    nrmmetd.m
    grpsubf
    syl
    #
    @0
    cX
    cr
    cF
    c.mi
    fco
    syl2anc
    wph
    @15
    va
    vb
    cX
    cX
    wph
    @3
    cX
    wcel
    #
    @4
    cX
    wcel
    #
    wa
    #
    wa
    #
    @8
    @14
    @25
    @6
    @3
    @4
    c.mi
    co
    #
    cF
    cfv
    #
    cc0
    wceq
    #
    @26
    c.0
    wceq
    #
    @7
    @25
    @5
    @27
    cc0
    @25
    @3
    @4
    cop
    #
    @1
    cfv
    #
    @30
    c.mi
    cfv
    #
    cF
    cfv
    #
    @5
    @27
    wph
    @19
    @30
    @0
    wcel
    @31
    @33
    wceq
    @24
    @21
    @3
    @4
    cX
    cX
    opelxpi
    @0
    cX
    @30
    cF
    c.mi
    fvco3
    syl2an
    @3
    @4
    @1
    df-ov
    @26
    @32
    cF
    @3
    @4
    c.mi
    df-ov
    fveq2i
    3eqtr4g
    #
    eqeq1d
    wph
    @24
    @26
    cX
    wcel
    #
    @28
    @29
    wb
    #
    wph
    @20
    @24
    @35
    nrmmetd.g
    @20
    @22
    @23
    @35
    cX
    cG
    c.mi
    @3
    @4
    nrmmetd.x
    nrmmetd.m
    grpsubcl
    3expb
    sylan
    #
    wph
    vx
    cv
    #
    cF
    cfv
    #
    cc0
    wceq
    #
    @38
    c.0
    wceq
    #
    wb
    #
    vx
    cX
    wral
    #
    @35
    @36
    wph
    @42
    vx
    cX
    nrmmetd.1
    ralrimiva
    #
    @42
    @36
    vx
    @26
    cX
    @38
    @26
    wceq
    #
    @40
    @28
    @41
    @29
    @45
    @39
    @27
    cc0
    @38
    @26
    cF
    fveq2
    eqeq1d
    @38
    @26
    c.0
    eqeq1
    bibi12d
    rspccva
    sylan
    syldan
    wph
    @20
    @24
    @29
    @7
    wb
    #
    nrmmetd.g
    @20
    @22
    @23
    @46
    cX
    cG
    c.mi
    @3
    @4
    c.0
    nrmmetd.x
    nrmmetd.z
    nrmmetd.m
    grpsubeq0
    3expb
    sylan
    3bitrd
    @25
    @13
    vc
    cX
    wph
    @24
    @9
    cX
    wcel
    #
    @13
    wph
    @24
    @47
    wa
    #
    wa
    #
    @27
    @9
    @3
    c.mi
    co
    #
    cF
    cfv
    #
    @9
    @4
    c.mi
    co
    #
    cF
    cfv
    #
    caddc
    co
    #
    @5
    @12
    cle
    @49
    @27
    @3
    @9
    c.mi
    co
    #
    cF
    cfv
    #
    @4
    @9
    c.mi
    co
    #
    cF
    cfv
    #
    caddc
    co
    #
    @54
    @49
    cX
    cr
    @26
    cF
    wph
    @18
    @48
    nrmmetd.f
    adantr
    #
    wph
    @24
    @35
    @47
    @37
    adantrr
    ffvelrnd
    @49
    @56
    @58
    @49
    cX
    cr
    @55
    cF
    @60
    @49
    @20
    @22
    @47
    @55
    cX
    wcel
    #
    wph
    @20
    @48
    nrmmetd.g
    adantr
    #
    wph
    @22
    @23
    @47
    simprll
    #
    wph
    @24
    @47
    simprr
    #
    cX
    cG
    c.mi
    @3
    @9
    nrmmetd.x
    nrmmetd.m
    grpsubcl
    syl3anc
    #
    ffvelrnd
    #
    @49
    cX
    cr
    @57
    cF
    @60
    @49
    @20
    @23
    @47
    @57
    cX
    wcel
    #
    @62
    wph
    @22
    @23
    @47
    simprlr
    #
    @64
    cX
    cG
    c.mi
    @4
    @9
    nrmmetd.x
    nrmmetd.m
    grpsubcl
    syl3anc
    #
    ffvelrnd
    #
    readdcld
    @49
    @51
    @53
    @49
    cX
    cr
    @50
    cF
    @60
    @49
    @20
    @47
    @22
    @50
    cX
    wcel
    @62
    @64
    @63
    cX
    cG
    c.mi
    @9
    @3
    nrmmetd.x
    nrmmetd.m
    grpsubcl
    syl3anc
    ffvelrnd
    #
    @49
    cX
    cr
    @52
    cF
    @60
    @49
    @20
    @47
    @23
    @52
    cX
    wcel
    @62
    @64
    @68
    cX
    cG
    c.mi
    @9
    @4
    nrmmetd.x
    nrmmetd.m
    grpsubcl
    syl3anc
    ffvelrnd
    #
    readdcld
    @49
    @55
    @57
    c.mi
    co
    #
    cF
    cfv
    #
    @27
    @59
    cle
    @49
    @73
    @26
    cF
    @49
    @20
    @22
    @23
    @47
    @73
    @26
    wceq
    @62
    @63
    @68
    @64
    cX
    cG
    c.mi
    @3
    @4
    @9
    nrmmetd.x
    nrmmetd.m
    grpnnncan2
    syl13anc
    fveq2d
    @49
    @61
    @67
    @38
    vy
    cv
    #
    c.mi
    co
    #
    cF
    cfv
    #
    @39
    @75
    cF
    cfv
    #
    caddc
    co
    #
    cle
    wbr
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    @74
    @59
    cle
    wbr
    #
    @65
    @69
    wph
    @81
    @48
    wph
    @80
    vx
    vy
    cX
    cX
    nrmmetd.2
    ralrimivva
    #
    adantr
    @80
    @82
    @55
    @75
    c.mi
    co
    #
    cF
    cfv
    #
    @56
    @78
    caddc
    co
    #
    cle
    wbr
    vx
    vy
    @55
    @57
    cX
    cX
    @38
    @55
    wceq
    #
    @77
    @85
    @79
    @86
    cle
    @87
    @76
    @84
    cF
    @38
    @55
    @75
    c.mi
    oveq1
    fveq2d
    @87
    @39
    @56
    @78
    caddc
    @38
    @55
    cF
    fveq2
    oveq1d
    breq12d
    @75
    @57
    wceq
    #
    @85
    @74
    @86
    @59
    cle
    @88
    @84
    @73
    cF
    @75
    @57
    @55
    c.mi
    oveq2
    fveq2d
    @88
    @78
    @58
    @56
    caddc
    @75
    @57
    cF
    fveq2
    oveq2d
    breq12d
    rspc2va
    syl21anc
    eqbrtrrd
    @49
    @56
    @58
    @51
    @53
    @66
    @70
    @71
    @72
    wph
    @22
    @47
    @56
    @51
    cle
    wbr
    #
    @23
    @25
    @27
    @4
    @3
    c.mi
    co
    #
    cF
    cfv
    #
    cle
    wbr
    #
    wi
    wph
    @22
    @47
    wa
    #
    wa
    #
    @89
    wi
    #
    vb
    vc
    @4
    @9
    wceq
    #
    @25
    @94
    @92
    @89
    @96
    @24
    @93
    wph
    @96
    @23
    @47
    @22
    @4
    @9
    cX
    eleq1
    anbi2d
    anbi2d
    @96
    @27
    @56
    @91
    @51
    cle
    @96
    @26
    @55
    cF
    @4
    @9
    @3
    c.mi
    oveq2
    fveq2d
    @96
    @90
    @50
    cF
    @4
    @9
    @3
    c.mi
    oveq1
    fveq2d
    breq12d
    imbi12d
    @25
    c.0
    @90
    c.mi
    co
    #
    cF
    cfv
    #
    c.0
    cF
    cfv
    #
    @91
    caddc
    co
    #
    @27
    @91
    cle
    @25
    c.0
    cX
    wcel
    #
    @90
    cX
    wcel
    #
    @81
    @98
    @100
    cle
    wbr
    #
    @25
    @20
    @101
    wph
    @20
    @24
    nrmmetd.g
    adantr
    #
    cX
    cG
    c.0
    nrmmetd.x
    nrmmetd.z
    grpidcl
    #
    syl
    @25
    @20
    @23
    @22
    @102
    @104
    wph
    @22
    @23
    simprr
    #
    wph
    @22
    @23
    simprl
    #
    cX
    cG
    c.mi
    @4
    @3
    nrmmetd.x
    nrmmetd.m
    grpsubcl
    syl3anc
    #
    wph
    @81
    @24
    @83
    adantr
    @80
    @103
    c.0
    @75
    c.mi
    co
    #
    cF
    cfv
    #
    @99
    @78
    caddc
    co
    #
    cle
    wbr
    vx
    vy
    c.0
    @90
    cX
    cX
    @41
    @77
    @110
    @79
    @111
    cle
    @41
    @76
    @109
    cF
    @38
    c.0
    @75
    c.mi
    oveq1
    fveq2d
    @41
    @39
    @99
    @78
    caddc
    @38
    c.0
    cF
    fveq2
    #
    oveq1d
    breq12d
    @75
    @90
    wceq
    #
    @110
    @98
    @111
    @100
    cle
    @113
    @109
    @97
    cF
    @75
    @90
    c.0
    c.mi
    oveq2
    fveq2d
    @113
    @78
    @91
    @99
    caddc
    @75
    @90
    cF
    fveq2
    oveq2d
    breq12d
    rspc2va
    syl21anc
    @25
    @97
    @26
    cF
    @25
    @90
    cG
    cminusg
    cfv
    #
    cfv
    #
    @97
    @26
    @25
    @20
    @102
    @115
    @97
    wceq
    @104
    @108
    cX
    cG
    c.mi
    @114
    @90
    c.0
    nrmmetd.x
    nrmmetd.m
    @114
    eqid
    #
    nrmmetd.z
    grpinvval2
    syl2anc
    @25
    @20
    @23
    @22
    @115
    @26
    wceq
    @104
    @106
    @107
    cX
    cG
    c.mi
    @114
    @4
    @3
    nrmmetd.x
    nrmmetd.m
    @116
    grpinvsub
    syl3anc
    eqtr3d
    fveq2d
    @25
    @100
    cc0
    @91
    caddc
    co
    @91
    @25
    @99
    cc0
    @91
    caddc
    wph
    @99
    cc0
    wceq
    #
    @24
    wph
    @43
    @101
    @117
    @44
    wph
    @20
    @101
    nrmmetd.g
    @105
    syl
    @42
    @117
    vx
    c.0
    cX
    @41
    @40
    @42
    @117
    @41
    @40
    @41
    @40
    wb
    @42
    @41
    @40
    pm5.501
    @41
    @40
    bicom
    syl6bb
    @41
    @39
    @99
    cc0
    @112
    eqeq1d
    bitr3d
    rspccva
    syl2anc
    adantr
    oveq1d
    @25
    @91
    @25
    @91
    @25
    cX
    cr
    @90
    cF
    wph
    @18
    @24
    nrmmetd.f
    adantr
    @108
    ffvelrnd
    recnd
    addid2d
    eqtrd
    3brtr3d
    chvarv
    #
    adantrlr
    wph
    @23
    @47
    @58
    @53
    cle
    wbr
    #
    @22
    @95
    wph
    @23
    @47
    wa
    #
    wa
    #
    @119
    wi
    va
    vb
    @7
    @94
    @121
    @89
    @119
    @7
    @93
    @120
    wph
    @7
    @22
    @23
    @47
    @3
    @4
    cX
    eleq1
    anbi1d
    anbi2d
    @7
    @56
    @58
    @51
    @53
    cle
    @7
    @55
    @57
    cF
    @3
    @4
    @9
    c.mi
    oveq1
    fveq2d
    @7
    @50
    @52
    cF
    @3
    @4
    @9
    c.mi
    oveq2
    fveq2d
    breq12d
    imbi12d
    @118
    chvarv
    adantrll
    le2addd
    letrd
    wph
    @24
    @5
    @27
    wceq
    @47
    @34
    adantrr
    @49
    @10
    @51
    @11
    @53
    caddc
    @49
    @9
    @3
    cop
    #
    @1
    cfv
    #
    @122
    c.mi
    cfv
    #
    cF
    cfv
    #
    @10
    @51
    @49
    @19
    @122
    @0
    wcel
    #
    @123
    @125
    wceq
    wph
    @19
    @48
    @21
    adantr
    #
    @49
    @47
    @22
    @126
    @64
    @63
    @9
    @3
    cX
    cX
    opelxpi
    syl2anc
    @0
    cX
    @122
    cF
    c.mi
    fvco3
    syl2anc
    @9
    @3
    @1
    df-ov
    @50
    @124
    cF
    @9
    @3
    c.mi
    df-ov
    fveq2i
    3eqtr4g
    @49
    @9
    @4
    cop
    #
    @1
    cfv
    #
    @128
    c.mi
    cfv
    #
    cF
    cfv
    #
    @11
    @53
    @49
    @19
    @128
    @0
    wcel
    #
    @129
    @131
    wceq
    @127
    @49
    @47
    @23
    @132
    @64
    @68
    @9
    @4
    cX
    cX
    opelxpi
    syl2anc
    @0
    cX
    @128
    cF
    c.mi
    fvco3
    syl2anc
    @9
    @4
    @1
    df-ov
    @52
    @130
    cF
    @9
    @4
    c.mi
    df-ov
    fveq2i
    3eqtr4g
    oveq12d
    3brtr4d
    expr
    ralrimiv
    jca
    ralrimivva
    cX
    cvv
    wcel
    @17
    @2
    @16
    wa
    wb
    cX
    cG
    cbs
    cfv
    cvv
    nrmmetd.x
    cG
    cbs
    fvex
    eqeltri
    va
    vb
    vc
    cvv
    @1
    cX
    ismet
    ax-mp
    sylanbrc
end
