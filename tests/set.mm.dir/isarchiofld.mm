include "cofld.mm"
include "wcel.mm"
include "carchi.mm"
include "c0g.mm"
include "cfv.mm"
include "cv.mm"
include "wbr.mm"
include "cmg.mm"
include "co.mm"
include "cn.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "corng.mm"
include "cogrp.mm"
include "wb.mm"
include "cfield.mm"
include "isofld.mm"
include "simprbi.mm"
include "orngogrp.mm"
include "eqid.mm"
include "isarchi3.mm"
include "3syl.mm"
include "cur.mm"
include "crg.mm"
include "orngring.mm"
include "ringidcl.mm"
include "wceq.mm"
include "breq2.mm"
include "oveq2.mm"
include "breq2d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "rspcv.mm"
include "syl.mm"
include "ofldlt1.mm"
include "pm5.5.mm"
include "sylibd.mm"
include "wa.mm"
include "cz.mm"
include "nnz.mm"
include "zrhmulg.mm"
include "syl2an.mm"
include "rexbidva.mm"
include "sylibrd.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "cdvr.mm"
include "cui.mm"
include "ad3antrrr.mm"
include "simplrr.mm"
include "wne.mm"
include "simplrl.mm"
include "simpr.mm"
include "simplll.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "grpidcl.mm"
include "pltne.mm"
include "syl3anc.mm"
include "mpd.mm"
include "necomd.mm"
include "cdr.mm"
include "simplbi.mm"
include "ccrg.mm"
include "isfld.mm"
include "drngunit.mm"
include "mpbir2and.mm"
include "dvrcl.mm"
include "breq1.mm"
include "cbvralv.mm"
include "sylib.mm"
include "ad2antrr.mm"
include "sylc.mm"
include "cmulr.mm"
include "simp-4l.mm"
include "simp-4r.mm"
include "simprd.mm"
include "simpld.mm"
include "simpllr.mm"
include "simplr.mm"
include "syl2anc.mm"
include "mulgcl.mm"
include "eqeltrd.mm"
include "orngrmullt.mm"
include "dvrcan1.mm"
include "oveq1d.mm"
include "mulgass2.mm"
include "syl13anc.mm"
include "ringlidm.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "3brtr3d.mm"
include "ex.mm"
include "reximdva.mm"
include "adantllr.mm"
include "expr.mm"
include "ralrimi.mm"
include "ralrimiva.mm"
include "impbid.mm"
include "bitrd.mm"

theorem isarchiofld
  let vx: setvar x
  let cB: class B
  let c.lt: class .<
  let vn: setvar n
  let cH: class H
  let cW: class W
  let vy: setvar y
  let vz: setvar z
  assume isarchiofld.b: |- B = ( Base ` W )
  assume isarchiofld.h: |- H = ( ZRHom ` W )
  assume isarchiofld.l: |- .< = ( lt ` W )

  disjoint n x
  disjoint B n
  disjoint B x
  disjoint W n
  disjoint W x
  disjoint H x
  disjoint .< n
  disjoint .< x
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint W y
  disjoint W z
  disjoint H y
  disjoint H z
  disjoint .< y
  disjoint .< z
  assert |- ( W e. oField -> ( W e. Archi <-> A. x e. B E. n e. NN x .< ( H ` n ) ) )

  proof
    cW
    cofld
    wcel
    #
    cW
    carchi
    wcel
    #
    cW
    c0g
    cfv
    #
    vy
    cv
    #
    c.lt
    wbr
    #
    vx
    cv
    #
    vn
    cv
    #
    @3
    cW
    cmg
    cfv
    #
    co
    #
    c.lt
    wbr
    #
    vn
    cn
    wrex
    #
    wi
    #
    vx
    cB
    wral
    #
    vy
    cB
    wral
    #
    @5
    @6
    cH
    cfv
    #
    c.lt
    wbr
    #
    vn
    cn
    wrex
    #
    vx
    cB
    wral
    #
    @0
    cW
    corng
    wcel
    #
    cW
    cogrp
    wcel
    @1
    @13
    wb
    @0
    cW
    cfield
    wcel
    #
    @18
    cW
    isofld
    #
    simprbi
    #
    cW
    orngogrp
    vy
    vx
    cB
    c.lt
    @7
    vn
    cW
    @2
    isarchiofld.b
    @2
    eqid
    #
    isarchiofld.l
    @7
    eqid
    #
    isarchi3
    3syl
    @0
    @13
    @17
    @0
    @13
    @5
    @6
    cW
    cur
    cfv
    #
    @7
    co
    #
    c.lt
    wbr
    #
    vn
    cn
    wrex
    #
    vx
    cB
    wral
    #
    @17
    @0
    @13
    @2
    @24
    c.lt
    wbr
    #
    @27
    wi
    #
    vx
    cB
    wral
    #
    @28
    @0
    @24
    cB
    wcel
    #
    @13
    @31
    wi
    @0
    @18
    cW
    crg
    wcel
    #
    @32
    @21
    cW
    orngring
    #
    cB
    cW
    @24
    isarchiofld.b
    @24
    eqid
    #
    ringidcl
    #
    3syl
    @12
    @31
    vy
    @24
    cB
    @3
    @24
    wceq
    #
    @11
    @30
    vx
    cB
    @37
    @4
    @29
    @10
    @27
    @3
    @24
    @2
    c.lt
    breq2
    @37
    @9
    @26
    vn
    cn
    @37
    @8
    @25
    @5
    c.lt
    @3
    @24
    @6
    @7
    oveq2
    breq2d
    rexbidv
    imbi12d
    ralbidv
    rspcv
    syl
    @0
    @30
    @27
    vx
    cB
    @0
    @29
    @30
    @27
    wb
    c.lt
    @24
    cW
    @2
    @22
    @35
    isarchiofld.l
    ofldlt1
    @29
    @27
    pm5.5
    syl
    ralbidv
    sylibd
    @0
    @16
    @27
    vx
    cB
    @0
    @15
    @26
    vn
    cn
    @0
    @6
    cn
    wcel
    #
    wa
    @14
    @25
    @5
    c.lt
    @0
    @33
    @6
    cz
    wcel
    #
    @14
    @25
    wceq
    #
    @38
    @0
    @18
    @33
    @21
    @34
    syl
    #
    @6
    nnz
    #
    cW
    @7
    @24
    cH
    @6
    isarchiofld.h
    @23
    @35
    zrhmulg
    syl2an
    #
    breq2d
    rexbidva
    ralbidv
    sylibrd
    @0
    @17
    @13
    @0
    @17
    wa
    #
    @12
    vy
    cB
    @44
    @3
    cB
    wcel
    #
    wa
    @11
    vx
    cB
    @44
    @45
    vx
    @0
    @17
    vx
    @0
    vx
    nfv
    @16
    vx
    cB
    nfra1
    nfan
    @45
    vx
    nfv
    nfan
    @44
    @45
    @5
    cB
    wcel
    #
    @11
    @44
    @45
    @46
    wa
    #
    wa
    #
    @4
    @10
    @48
    @4
    wa
    #
    @5
    @3
    cW
    cdvr
    cfv
    #
    co
    #
    @14
    c.lt
    wbr
    #
    vn
    cn
    wrex
    #
    @10
    @49
    @51
    cB
    wcel
    #
    vz
    cv
    #
    @14
    c.lt
    wbr
    #
    vn
    cn
    wrex
    #
    vz
    cB
    wral
    #
    @53
    @49
    @33
    @46
    @3
    cW
    cui
    cfv
    #
    wcel
    #
    @54
    @0
    @33
    @17
    @47
    @4
    @41
    ad3antrrr
    #
    @44
    @45
    @46
    @4
    simplrr
    @49
    @60
    @45
    @3
    @2
    wne
    #
    @44
    @45
    @46
    @4
    simplrl
    #
    @49
    @2
    @3
    @49
    @4
    @2
    @3
    wne
    #
    @48
    @4
    simpr
    @49
    @0
    @2
    cB
    wcel
    #
    @45
    @4
    @64
    wi
    #
    @0
    @17
    @47
    @4
    simplll
    #
    @49
    @33
    cW
    cgrp
    wcel
    #
    @65
    @61
    cW
    ringgrp
    #
    cB
    cW
    @2
    isarchiofld.b
    @22
    grpidcl
    #
    3syl
    @63
    cofld
    cB
    cB
    c.lt
    cW
    @2
    @3
    isarchiofld.l
    pltne
    #
    syl3anc
    mpd
    necomd
    @49
    @0
    cW
    cdr
    wcel
    #
    @60
    @45
    @62
    wa
    wb
    #
    @67
    @0
    @19
    @72
    @0
    @19
    @18
    @20
    simplbi
    @19
    @72
    cW
    ccrg
    wcel
    cW
    isfld
    simplbi
    syl
    #
    cB
    cW
    @59
    @3
    @2
    isarchiofld.b
    @59
    eqid
    #
    @22
    drngunit
    #
    3syl
    mpbir2and
    cB
    @50
    cW
    @59
    @5
    @3
    isarchiofld.b
    @75
    @50
    eqid
    #
    dvrcl
    #
    syl3anc
    @44
    @58
    @47
    @4
    @44
    @17
    @58
    @0
    @17
    simpr
    @16
    @57
    vx
    vz
    cB
    @5
    @55
    wceq
    @15
    @56
    vn
    cn
    @5
    @55
    @14
    c.lt
    breq1
    rexbidv
    cbvralv
    sylib
    ad2antrr
    @57
    @53
    vz
    @51
    cB
    @55
    @51
    wceq
    @56
    @52
    vn
    cn
    @55
    @51
    @14
    c.lt
    breq1
    rexbidv
    rspcv
    sylc
    @0
    @47
    @4
    @53
    @10
    wi
    @17
    @0
    @47
    wa
    #
    @4
    wa
    #
    @52
    @9
    vn
    cn
    @80
    @38
    wa
    #
    @52
    @9
    @81
    @52
    wa
    #
    @51
    @3
    cW
    cmulr
    cfv
    #
    co
    #
    @14
    @3
    @83
    co
    #
    @5
    @8
    c.lt
    @82
    cB
    cW
    c.lt
    @83
    @51
    @14
    @2
    @3
    isarchiofld.b
    @83
    eqid
    #
    @22
    @82
    @0
    @18
    @0
    @47
    @4
    @38
    @52
    simp-4l
    #
    @21
    syl
    @82
    @33
    @46
    @60
    @54
    @82
    @0
    @33
    @87
    @41
    syl
    #
    @82
    @45
    @46
    @0
    @47
    @4
    @38
    @52
    simp-4r
    #
    simprd
    #
    @82
    @60
    @45
    @62
    @82
    @45
    @46
    @89
    simpld
    #
    @82
    @2
    @3
    @82
    @4
    @64
    @79
    @4
    @38
    @52
    simpllr
    #
    @82
    @0
    @65
    @45
    @66
    @87
    @82
    @33
    @68
    @65
    @88
    @69
    @70
    3syl
    @91
    @71
    syl3anc
    mpd
    necomd
    @82
    @0
    @72
    @73
    @87
    @74
    @76
    3syl
    mpbir2and
    #
    @78
    syl3anc
    @82
    @14
    @25
    cB
    @82
    @0
    @38
    @40
    @87
    @80
    @38
    @52
    simplr
    #
    @43
    syl2anc
    #
    @82
    @68
    @39
    @32
    @25
    cB
    wcel
    @82
    @33
    @68
    @88
    @69
    syl
    @82
    @38
    @39
    @94
    @42
    syl
    #
    @82
    @33
    @32
    @88
    @36
    syl
    #
    cB
    @7
    cW
    @6
    @24
    isarchiofld.b
    @23
    mulgcl
    syl3anc
    eqeltrd
    @91
    isarchiofld.l
    @82
    @0
    @72
    @87
    @74
    syl
    @81
    @52
    simpr
    @92
    orngrmullt
    @82
    @33
    @46
    @60
    @84
    @5
    wceq
    @88
    @90
    @93
    cB
    @50
    cW
    @83
    @59
    @5
    @3
    isarchiofld.b
    @75
    @77
    @86
    dvrcan1
    syl3anc
    @82
    @85
    @25
    @3
    @83
    co
    #
    @6
    @24
    @3
    @83
    co
    #
    @7
    co
    #
    @8
    @82
    @14
    @25
    @3
    @83
    @95
    oveq1d
    @82
    @33
    @39
    @32
    @45
    @98
    @100
    wceq
    @88
    @96
    @97
    @91
    cB
    cW
    @7
    @83
    @6
    @24
    @3
    isarchiofld.b
    @23
    @86
    mulgass2
    syl13anc
    @82
    @99
    @3
    @6
    @7
    @82
    @33
    @45
    @99
    @3
    wceq
    @88
    @91
    cB
    cW
    @83
    @24
    @3
    isarchiofld.b
    @86
    @35
    ringlidm
    syl2anc
    oveq2d
    3eqtrd
    3brtr3d
    ex
    reximdva
    adantllr
    mpd
    ex
    expr
    ralrimi
    ralrimiva
    ex
    impbid
    bitrd
end
