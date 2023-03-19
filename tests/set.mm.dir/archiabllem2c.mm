include "co.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "csg.mm"
include "cfv.mm"
include "wfal.mm"
include "wcel.mm"
include "simprr.mm"
include "wn.mm"
include "w3a.mm"
include "c1.mm"
include "caddc.mm"
include "cz.mm"
include "cneg.mm"
include "cminusg.mm"
include "cogrp.mm"
include "simpl1l.mm"
include "syl.mm"
include "simpl1r.mm"
include "cgrp.mm"
include "adantr.mm"
include "ogrpgrp.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "syl2anc.mm"
include "3syl.mm"
include "simpr2.mm"
include "peano2zd.mm"
include "simp2.mm"
include "mulgcl.mm"
include "simpr1.mm"
include "3ad2ant1.mm"
include "comnd.mm"
include "isogrp.mm"
include "simprbi.mm"
include "simpr3.mm"
include "simprd.mm"
include "simpld.mm"
include "coppg.mm"
include "omndadd2rd.mm"
include "eqid.mm"
include "ogrpsub.mm"
include "syl131anc.mm"
include "c2.mm"
include "zcnd.mm"
include "1cnd.mm"
include "add4d.mm"
include "cc.mm"
include "wceq.mm"
include "1p1e2.mm"
include "oveq2i.mm"
include "addcom.mm"
include "oveq1d.mm"
include "syl5eq.mm"
include "2cnd.mm"
include "simpr.mm"
include "simpl.mm"
include "addcld.mm"
include "addcomd.mm"
include "eqtr4d.mm"
include "eqtr3d.mm"
include "2z.mm"
include "a1i.mm"
include "zaddcld.mm"
include "mulgdir.mm"
include "syl13anc.mm"
include "eqtrd.mm"
include "mulg2.mm"
include "3eqtr3d.mm"
include "breqtrd.mm"
include "eqeltrrd.mm"
include "grpsubval.mm"
include "grpinvcl.mm"
include "znegcld.mm"
include "ogrpaddlt.mm"
include "ogrpaddltrd.mm"
include "cpo.mm"
include "wi.mm"
include "ctos.mm"
include "omndtos.mm"
include "tospos.mm"
include "plttr.mm"
include "mp2and.mm"
include "eqbrtrd.mm"
include "wb.mm"
include "eqeltrd.mm"
include "ogrpinvlt.mm"
include "syl211anc.mm"
include "mpbid.mm"
include "mulgneg.mm"
include "breqtrrd.mm"
include "grpsubcl.mm"
include "plelttr.mm"
include "grpass.mm"
include "cc0.mm"
include "negidd.mm"
include "mulg0.mm"
include "oveq2d.mm"
include "grprid.mm"
include "3eqtrd.mm"
include "3anassrs.mm"
include "wrex.mm"
include "carchi.mm"
include "simp3.mm"
include "archirngz.mm"
include "reeanv.mm"
include "sylanbrc.mm"
include "r19.29vva.mm"
include "tltnle.mm"
include "3expa.mm"
include "adantrr.mm"
include "pm2.21fal.mm"
include "3adant1r.mm"
include "grpsubid.mm"
include "ogrpsublt.mm"
include "eqbrtrrd.mm"
include "archiabllem2a.mm"
include "r19.29a.mm"
include "inegd.mm"

theorem archiabllem2c
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let c.lt: class .<
  let c.x: class .x.
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vn: setvar n
  let vt: setvar t
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cU: class U
  assume archiabllem.b: |- B = ( Base ` W )
  assume archiabllem.0: |- .0. = ( 0g ` W )
  assume archiabllem.e: |- .<_ = ( le ` W )
  assume archiabllem.t: |- .< = ( lt ` W )
  assume archiabllem.m: |- .x. = ( .g ` W )
  assume archiabllem.g: |- ( ph -> W e. oGrp )
  assume archiabllem.a: |- ( ph -> W e. Archi )
  assume archiabllem2.1: |- .+ = ( +g ` W )
  assume archiabllem2.2: |- ( ph -> ( oppG ` W ) e. oGrp )
  assume archiabllem2.3: |- ( ( ph /\ a e. B /\ .0. .< a ) -> E. b e. B ( .0. .< b /\ b .< a ) )
  assume archiabllem2b.4: |- ( ph -> X e. B )
  assume archiabllem2b.5: |- ( ph -> Y e. B )

  disjoint a b
  disjoint B a
  disjoint B b
  disjoint W a
  disjoint W b
  disjoint X a
  disjoint X b
  disjoint Y a
  disjoint Y b
  disjoint a ph
  disjoint b ph
  disjoint .+ a
  disjoint .+ b
  disjoint .<_ a
  disjoint .<_ b
  disjoint .< a
  disjoint .< b
  disjoint .0. a
  disjoint .0. b
  disjoint a b
  disjoint m n
  disjoint m t
  disjoint n t
  disjoint a c
  disjoint a t
  disjoint b c
  disjoint b t
  disjoint c t
  disjoint B c
  disjoint B t
  disjoint W c
  disjoint W t
  disjoint X c
  disjoint X t
  disjoint a m
  disjoint a n
  disjoint b m
  disjoint b n
  disjoint Y m
  disjoint Y n
  disjoint Y t
  disjoint ph t
  disjoint c m
  disjoint c n
  disjoint .+ c
  disjoint .+ t
  disjoint .+ m
  disjoint .+ n
  disjoint .<_ c
  disjoint .<_ t
  disjoint .<_ m
  disjoint .<_ n
  disjoint .< c
  disjoint .< t
  disjoint .< m
  disjoint .< n
  disjoint .0. c
  disjoint .0. t
  disjoint a m
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b m
  disjoint b n
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B m
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint U m
  disjoint U n
  disjoint U x
  disjoint W m
  disjoint W n
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint X m
  disjoint X n
  disjoint X x
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint .x. m
  disjoint .x. n
  disjoint .x. x
  disjoint .0. m
  disjoint .0. n
  disjoint .0. x
  disjoint .< m
  disjoint .< n
  disjoint .< x
  disjoint .<_ m
  disjoint .<_ x
  assert |- ( ph -> -. ( X .+ Y ) .< ( Y .+ X ) )

  proof
    wph
    cX
    cY
    c.pl
    co
    #
    cY
    cX
    c.pl
    co
    #
    c.lt
    wbr
    #
    wph
    @2
    wa
    #
    c.0
    vt
    cv
    #
    c.lt
    wbr
    #
    @4
    @4
    c.pl
    co
    #
    @1
    @0
    cW
    csg
    cfv
    #
    co
    #
    c.le
    wbr
    #
    wa
    #
    wfal
    vt
    cB
    @3
    @4
    cB
    wcel
    #
    wa
    #
    @10
    wa
    @9
    @12
    @5
    @9
    simprr
    @12
    @5
    @9
    wn
    #
    @9
    @3
    @11
    @5
    @13
    @3
    @11
    @5
    w3a
    #
    @8
    @6
    c.lt
    wbr
    #
    @13
    @14
    vn
    cv
    #
    @4
    c.x
    co
    #
    cX
    c.lt
    wbr
    #
    cX
    @16
    c1
    caddc
    co
    #
    @4
    c.x
    co
    #
    c.le
    wbr
    #
    wa
    #
    vm
    cv
    #
    @4
    c.x
    co
    #
    cY
    c.lt
    wbr
    #
    cY
    @23
    c1
    caddc
    co
    #
    @4
    c.x
    co
    #
    c.le
    wbr
    #
    wa
    #
    wa
    #
    @15
    vn
    vm
    cz
    cz
    @14
    @16
    cz
    wcel
    #
    @23
    cz
    wcel
    #
    @30
    @15
    @14
    @31
    @32
    @30
    w3a
    #
    wa
    #
    @8
    @6
    @16
    @23
    caddc
    co
    #
    @4
    c.x
    co
    #
    c.pl
    co
    #
    @35
    cneg
    #
    @4
    c.x
    co
    #
    c.pl
    co
    #
    @6
    c.lt
    @34
    @8
    @37
    @0
    cW
    cminusg
    cfv
    #
    cfv
    #
    c.pl
    co
    #
    c.le
    wbr
    #
    @43
    @40
    c.lt
    wbr
    #
    @8
    @40
    c.lt
    wbr
    #
    @34
    @8
    @37
    @0
    @7
    co
    #
    @43
    c.le
    @34
    @8
    @27
    @20
    c.pl
    co
    #
    @0
    @7
    co
    #
    @47
    c.le
    @34
    cW
    cogrp
    wcel
    #
    @1
    cB
    wcel
    #
    @48
    cB
    wcel
    #
    @0
    cB
    wcel
    #
    @1
    @48
    c.le
    wbr
    @8
    @49
    c.le
    wbr
    @34
    wph
    @50
    wph
    @2
    @11
    @5
    @33
    simpl1l
    #
    archiabllem.g
    syl
    #
    @34
    wph
    @2
    @51
    @54
    wph
    @2
    @11
    @5
    @33
    simpl1r
    @3
    cW
    cgrp
    wcel
    #
    cY
    cB
    wcel
    #
    cX
    cB
    wcel
    #
    @51
    @3
    @50
    @56
    wph
    @50
    @2
    archiabllem.g
    adantr
    #
    cW
    ogrpgrp
    #
    syl
    #
    wph
    @57
    @2
    archiabllem2b.5
    adantr
    #
    wph
    @58
    @2
    archiabllem2b.4
    adantr
    #
    cB
    c.pl
    cW
    cY
    cX
    archiabllem.b
    archiabllem2.1
    grpcl
    syl3anc
    #
    syl2anc
    #
    @34
    @56
    @27
    cB
    wcel
    #
    @20
    cB
    wcel
    #
    @52
    @34
    wph
    @50
    @56
    @54
    archiabllem.g
    @60
    3syl
    #
    @34
    @56
    @26
    cz
    wcel
    #
    @11
    @66
    @68
    @34
    @23
    @14
    @31
    @32
    @30
    simpr2
    #
    peano2zd
    #
    @14
    @11
    @33
    @3
    @11
    @5
    simp2
    #
    adantr
    #
    cB
    c.x
    cW
    @26
    @4
    archiabllem.b
    archiabllem.m
    mulgcl
    syl3anc
    #
    @34
    @56
    @19
    cz
    wcel
    #
    @11
    @67
    @68
    @34
    @16
    @14
    @31
    @32
    @30
    simpr1
    #
    peano2zd
    #
    @73
    cB
    c.x
    cW
    @19
    @4
    archiabllem.b
    archiabllem.m
    mulgcl
    syl3anc
    #
    cB
    c.pl
    cW
    @27
    @20
    archiabllem.b
    archiabllem2.1
    grpcl
    syl3anc
    #
    @34
    @56
    @58
    @57
    @53
    @68
    @14
    @58
    @33
    @3
    @11
    @58
    @5
    @63
    3ad2ant1
    #
    adantr
    #
    @14
    @57
    @33
    @3
    @11
    @57
    @5
    @62
    3ad2ant1
    #
    adantr
    #
    cB
    c.pl
    cW
    cX
    cY
    archiabllem.b
    archiabllem2.1
    grpcl
    #
    syl3anc
    #
    @34
    cB
    c.pl
    c.le
    cW
    @20
    cY
    cX
    @27
    archiabllem.b
    archiabllem.e
    archiabllem2.1
    @34
    wph
    @50
    cW
    comnd
    wcel
    #
    @54
    archiabllem.g
    @50
    @56
    @86
    cW
    isogrp
    simprbi
    #
    3syl
    #
    @78
    @83
    @81
    @74
    @34
    @25
    @28
    @34
    @22
    @29
    @14
    @31
    @32
    @30
    simpr3
    #
    simprd
    #
    simprd
    @34
    @18
    @21
    @34
    @22
    @29
    @89
    simpld
    #
    simprd
    @34
    wph
    cW
    coppg
    cfv
    #
    cogrp
    wcel
    #
    @92
    comnd
    wcel
    #
    @54
    archiabllem2.2
    @93
    @92
    cgrp
    wcel
    @94
    @92
    isogrp
    simprbi
    3syl
    omndadd2rd
    cB
    cW
    c.le
    @7
    @1
    @48
    @0
    archiabllem.b
    archiabllem.e
    @7
    eqid
    #
    ogrpsub
    syl131anc
    @34
    @48
    @37
    @0
    @7
    @34
    @26
    @19
    caddc
    co
    #
    @4
    c.x
    co
    #
    c2
    @4
    c.x
    co
    #
    @36
    c.pl
    co
    #
    @48
    @37
    @34
    @97
    c2
    @35
    caddc
    co
    #
    @4
    c.x
    co
    #
    @99
    @34
    @96
    @100
    @4
    c.x
    @34
    @23
    @16
    caddc
    co
    #
    c1
    c1
    caddc
    co
    #
    caddc
    co
    #
    @96
    @100
    @34
    @23
    @16
    c1
    c1
    @34
    @23
    @70
    zcnd
    #
    @34
    @16
    @76
    zcnd
    #
    @34
    1cnd
    #
    @107
    add4d
    @34
    @23
    cc
    wcel
    #
    @16
    cc
    wcel
    #
    @104
    @100
    wceq
    @105
    @106
    @108
    @109
    wa
    #
    @104
    @35
    c2
    caddc
    co
    #
    @100
    @110
    @104
    @102
    c2
    caddc
    co
    @111
    @103
    c2
    @102
    caddc
    1p1e2
    oveq2i
    @110
    @102
    @35
    c2
    caddc
    @23
    @16
    addcom
    oveq1d
    syl5eq
    @110
    c2
    @35
    @110
    2cnd
    @110
    @16
    @23
    @108
    @109
    simpr
    @108
    @109
    simpl
    addcld
    addcomd
    eqtr4d
    syl2anc
    eqtr3d
    oveq1d
    @34
    @56
    c2
    cz
    wcel
    #
    @35
    cz
    wcel
    #
    @11
    @101
    @99
    wceq
    @68
    @112
    @34
    2z
    a1i
    @34
    @16
    @23
    @76
    @70
    zaddcld
    #
    @73
    cB
    c.pl
    c.x
    cW
    c2
    @35
    @4
    archiabllem.b
    archiabllem.m
    archiabllem2.1
    mulgdir
    syl13anc
    eqtrd
    @34
    @56
    @69
    @75
    @11
    @97
    @48
    wceq
    @68
    @71
    @77
    @73
    cB
    c.pl
    c.x
    cW
    @26
    @19
    @4
    archiabllem.b
    archiabllem.m
    archiabllem2.1
    mulgdir
    syl13anc
    @34
    @98
    @6
    @36
    c.pl
    @34
    @11
    @98
    @6
    wceq
    @73
    cB
    c.pl
    c.x
    cW
    @4
    archiabllem.b
    archiabllem.m
    archiabllem2.1
    mulg2
    syl
    oveq1d
    3eqtr3d
    #
    oveq1d
    breqtrd
    @34
    @37
    cB
    wcel
    #
    @53
    @47
    @43
    wceq
    @34
    @48
    @37
    cB
    @115
    @79
    eqeltrrd
    #
    @85
    cB
    c.pl
    cW
    @41
    @7
    @37
    @0
    archiabllem.b
    archiabllem2.1
    @41
    eqid
    #
    @95
    grpsubval
    syl2anc
    breqtrd
    @34
    cB
    c.pl
    c.lt
    cW
    cogrp
    @42
    @39
    @37
    archiabllem.b
    archiabllem.t
    archiabllem2.1
    @55
    @34
    wph
    @93
    @54
    archiabllem2.2
    syl
    #
    @34
    @56
    @53
    @42
    cB
    wcel
    #
    @68
    @85
    cB
    cW
    @41
    @0
    archiabllem.b
    @118
    grpinvcl
    syl2anc
    #
    @34
    @56
    @38
    cz
    wcel
    #
    @11
    @39
    cB
    wcel
    #
    @68
    @34
    @35
    @114
    znegcld
    #
    @73
    cB
    c.x
    cW
    @38
    @4
    archiabllem.b
    archiabllem.m
    mulgcl
    syl3anc
    #
    @117
    @34
    @42
    @36
    @41
    cfv
    #
    @39
    c.lt
    @34
    @36
    @0
    c.lt
    wbr
    #
    @42
    @126
    c.lt
    wbr
    #
    @34
    @36
    @17
    @24
    c.pl
    co
    #
    @0
    c.lt
    @34
    @56
    @31
    @32
    @11
    @36
    @129
    wceq
    @68
    @76
    @70
    @73
    cB
    c.pl
    c.x
    cW
    @16
    @23
    @4
    archiabllem.b
    archiabllem.m
    archiabllem2.1
    mulgdir
    syl13anc
    #
    @34
    @129
    cX
    @24
    c.pl
    co
    #
    c.lt
    wbr
    #
    @131
    @0
    c.lt
    wbr
    #
    @129
    @0
    c.lt
    wbr
    #
    @34
    @50
    @17
    cB
    wcel
    #
    @58
    @24
    cB
    wcel
    #
    @18
    @132
    @55
    @34
    @56
    @31
    @11
    @135
    @68
    @76
    @73
    cB
    c.x
    cW
    @16
    @4
    archiabllem.b
    archiabllem.m
    mulgcl
    syl3anc
    #
    @81
    @34
    @56
    @32
    @11
    @136
    @68
    @70
    @73
    cB
    c.x
    cW
    @23
    @4
    archiabllem.b
    archiabllem.m
    mulgcl
    syl3anc
    #
    @34
    @18
    @21
    @91
    simpld
    cB
    c.pl
    c.lt
    cW
    @17
    cX
    @24
    archiabllem.b
    archiabllem.t
    archiabllem2.1
    ogrpaddlt
    syl131anc
    @34
    cB
    c.pl
    c.lt
    cW
    cogrp
    @24
    cY
    cX
    archiabllem.b
    archiabllem.t
    archiabllem2.1
    @55
    @119
    @138
    @83
    @81
    @34
    @25
    @28
    @90
    simpld
    ogrpaddltrd
    @34
    cW
    cpo
    wcel
    #
    @129
    cB
    wcel
    #
    @131
    cB
    wcel
    #
    @53
    @132
    @133
    wa
    @134
    wi
    @34
    @86
    cW
    ctos
    wcel
    #
    @139
    @88
    cW
    omndtos
    #
    cW
    tospos
    3syl
    #
    @34
    @56
    @135
    @136
    @140
    @68
    @137
    @138
    cB
    c.pl
    cW
    @17
    @24
    archiabllem.b
    archiabllem2.1
    grpcl
    syl3anc
    #
    @34
    @56
    @58
    @136
    @141
    @68
    @81
    @138
    cB
    c.pl
    cW
    cX
    @24
    archiabllem.b
    archiabllem2.1
    grpcl
    syl3anc
    @85
    cB
    c.lt
    cW
    @129
    @131
    @0
    archiabllem.b
    archiabllem.t
    plttr
    syl13anc
    mp2and
    eqbrtrd
    @34
    @50
    @93
    @36
    cB
    wcel
    #
    @53
    @127
    @128
    wb
    @55
    @119
    @34
    @36
    @129
    cB
    @130
    @145
    eqeltrd
    #
    @85
    cB
    c.lt
    cW
    @41
    @36
    @0
    archiabllem.b
    archiabllem.t
    @118
    ogrpinvlt
    syl211anc
    mpbid
    @34
    @56
    @113
    @11
    @39
    @126
    wceq
    @68
    @114
    @73
    cB
    c.x
    cW
    @41
    @35
    @4
    archiabllem.b
    archiabllem.m
    @118
    mulgneg
    syl3anc
    breqtrrd
    ogrpaddltrd
    @34
    @139
    @8
    cB
    wcel
    #
    @43
    cB
    wcel
    #
    @40
    cB
    wcel
    #
    @44
    @45
    wa
    @46
    wi
    @144
    @34
    @56
    @51
    @53
    @148
    @68
    @65
    @85
    cB
    cW
    @7
    @1
    @0
    archiabllem.b
    @95
    grpsubcl
    #
    syl3anc
    @34
    @56
    @116
    @120
    @149
    @68
    @117
    @121
    cB
    c.pl
    cW
    @37
    @42
    archiabllem.b
    archiabllem2.1
    grpcl
    syl3anc
    @34
    @56
    @116
    @123
    @150
    @68
    @117
    @125
    cB
    c.pl
    cW
    @37
    @39
    archiabllem.b
    archiabllem2.1
    grpcl
    syl3anc
    cB
    c.lt
    cW
    c.le
    @8
    @43
    @40
    archiabllem.b
    archiabllem.e
    archiabllem.t
    plelttr
    syl13anc
    mp2and
    @34
    @40
    @6
    @36
    @39
    c.pl
    co
    #
    c.pl
    co
    #
    @6
    c.0
    c.pl
    co
    #
    @6
    @34
    @56
    @6
    cB
    wcel
    #
    @146
    @123
    @40
    @153
    wceq
    @68
    @34
    @56
    @11
    @11
    @155
    @68
    @73
    @73
    cB
    c.pl
    cW
    @4
    @4
    archiabllem.b
    archiabllem2.1
    grpcl
    #
    syl3anc
    #
    @147
    @125
    cB
    c.pl
    cW
    @6
    @36
    @39
    archiabllem.b
    archiabllem2.1
    grpass
    syl13anc
    @34
    @152
    c.0
    @6
    c.pl
    @34
    @35
    @38
    caddc
    co
    #
    @4
    c.x
    co
    #
    cc0
    @4
    c.x
    co
    #
    @152
    c.0
    @34
    @158
    cc0
    @4
    c.x
    @34
    @35
    @34
    @16
    @23
    @106
    @105
    addcld
    negidd
    oveq1d
    @34
    @56
    @113
    @122
    @11
    @159
    @152
    wceq
    @68
    @114
    @124
    @73
    cB
    c.pl
    c.x
    cW
    @35
    @38
    @4
    archiabllem.b
    archiabllem.m
    archiabllem2.1
    mulgdir
    syl13anc
    @34
    @11
    @160
    c.0
    wceq
    @73
    cB
    c.x
    cW
    @4
    c.0
    archiabllem.b
    archiabllem.0
    archiabllem.m
    mulg0
    syl
    3eqtr3d
    oveq2d
    @34
    @56
    @155
    @154
    @6
    wceq
    @68
    @157
    cB
    c.pl
    cW
    @6
    c.0
    archiabllem.b
    archiabllem2.1
    archiabllem.0
    grprid
    syl2anc
    3eqtrd
    breqtrd
    3anassrs
    @14
    @22
    vn
    cz
    wrex
    @29
    vm
    cz
    wrex
    @30
    vm
    cz
    wrex
    vn
    cz
    wrex
    @14
    cB
    c.lt
    c.x
    vn
    c.le
    cW
    @4
    cX
    c.0
    archiabllem.b
    archiabllem.0
    archiabllem.t
    archiabllem.e
    archiabllem.m
    @3
    @11
    @50
    @5
    @59
    3ad2ant1
    #
    @3
    @11
    cW
    carchi
    wcel
    #
    @5
    wph
    @162
    @2
    archiabllem.a
    adantr
    #
    3ad2ant1
    #
    @72
    @80
    @3
    @11
    @5
    simp3
    #
    @3
    @11
    @93
    @5
    wph
    @93
    @2
    archiabllem2.2
    adantr
    #
    3ad2ant1
    #
    archirngz
    @14
    cB
    c.lt
    c.x
    vm
    c.le
    cW
    @4
    cY
    c.0
    archiabllem.b
    archiabllem.0
    archiabllem.t
    archiabllem.e
    archiabllem.m
    @161
    @164
    @72
    @82
    @165
    @167
    archirngz
    @22
    @29
    vn
    vm
    cz
    cz
    reeanv
    sylanbrc
    r19.29vva
    @14
    @142
    @148
    @155
    @15
    @13
    wb
    @14
    @50
    @86
    @142
    @161
    @87
    @143
    3syl
    @3
    @11
    @148
    @5
    @3
    @56
    @51
    @53
    @148
    @61
    @64
    @3
    @56
    @58
    @57
    @53
    @61
    @63
    @62
    @84
    syl3anc
    #
    @151
    syl3anc
    #
    3ad2ant1
    @14
    @56
    @11
    @11
    @155
    @14
    @50
    @56
    @161
    @60
    syl
    @72
    @72
    @156
    syl3anc
    cB
    c.lt
    cW
    c.le
    @8
    @6
    archiabllem.b
    archiabllem.e
    archiabllem.t
    tltnle
    syl3anc
    mpbid
    3expa
    adantrr
    pm2.21fal
    @3
    cB
    c.pl
    c.lt
    c.x
    c.le
    cW
    @8
    c.0
    va
    vb
    vt
    archiabllem.b
    archiabllem.0
    archiabllem.e
    archiabllem.t
    archiabllem.m
    @59
    @163
    archiabllem2.1
    @166
    wph
    va
    cv
    #
    cB
    wcel
    c.0
    @170
    c.lt
    wbr
    c.0
    vb
    cv
    #
    c.lt
    wbr
    @171
    @170
    c.lt
    wbr
    wa
    vb
    cB
    wrex
    @2
    archiabllem2.3
    3adant1r
    @169
    @3
    @0
    @0
    @7
    co
    #
    c.0
    @8
    c.lt
    @3
    @56
    @53
    @172
    c.0
    wceq
    @61
    @168
    cB
    cW
    @7
    @0
    c.0
    archiabllem.b
    archiabllem.0
    @95
    grpsubid
    syl2anc
    @3
    @50
    @53
    @51
    @53
    @2
    @172
    @8
    c.lt
    wbr
    @59
    @168
    @64
    @168
    wph
    @2
    simpr
    cB
    c.lt
    cW
    @7
    @0
    @1
    @0
    archiabllem.b
    archiabllem.t
    @95
    ogrpsublt
    syl131anc
    eqbrtrrd
    archiabllem2a
    r19.29a
    inegd
end
