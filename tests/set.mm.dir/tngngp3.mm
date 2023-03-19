include "cr.mm"
include "wf.mm"
include "cngp.mm"
include "wcel.mm"
include "cgrp.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "co.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "w3a.mm"
include "wa.mm"
include "cvv.mm"
include "wi.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fex.mm"
include "mpan2.mm"
include "tnggrpr.mm"
include "simp2.mm"
include "cnm.mm"
include "c0g.mm"
include "cminusg.mm"
include "cplusg.mm"
include "eqid.mm"
include "nmeq0.mm"
include "nminv.mm"
include "nmtri.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "3jca.mm"
include "adantl.mm"
include "3ad2ant1.mm"
include "tngbas.mm"
include "tngplusg.mm"
include "eqidd.mm"
include "oveqd.mm"
include "adantr.mm"
include "grpinvpropd.mm"
include "syl5eq.mm"
include "reex.mm"
include "tngnm.mm"
include "3adant1.mm"
include "tng0.mm"
include "simp1.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "simp3.mm"
include "eqeq2d.mm"
include "bibi12d.mm"
include "fveq12d.mm"
include "eqeq12d.mm"
include "fveq1.mm"
include "oveq12d.mm"
include "3ad2ant2.mm"
include "breq12d.mm"
include "raleqbidv.mm"
include "3anbi123d.mm"
include "syl.mm"
include "mpbird.mm"
include "jca.mm"
include "3exp.mm"
include "mpd.mm"
include "expcom.mm"
include "com13.mm"
include "csg.mm"
include "simpl.mm"
include "weq.mm"
include "fveq2.mm"
include "eqeq1.mm"
include "fveq2d.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "ralbidv.mm"
include "rspccva.mm"
include "ex.mm"
include "imp.mm"
include "grpsubval.mm"
include "3simpc.mm"
include "ralimi.mm"
include "simpr.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rspc2v.mm"
include "grpinvcl.mm"
include "anim2d.mm"
include "syl11.mm"
include "expd.mm"
include "eqcomd.mm"
include "adantld.mm"
include "breqtrrd.mm"
include "impcom.mm"
include "eqbrtrd.mm"
include "tngngpd.mm"
include "impbid.mm"

theorem tngngp3
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let cT: class T
  let cG: class G
  let cI: class I
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let cV: class V
  let va: setvar a
  let vb: setvar b
  assume tngngp3.t: |- T = ( G toNrmGrp N )
  assume tngngp3.x: |- X = ( Base ` G )
  assume tngngp3.z: |- .0. = ( 0g ` G )
  assume tngngp3.p: |- .+ = ( +g ` G )
  assume tngngp3.i: |- I = ( invg ` G )

  disjoint G x
  disjoint G y
  disjoint x y
  disjoint N x
  disjoint N y
  disjoint T x
  disjoint T y
  disjoint X x
  disjoint X y
  disjoint I x
  disjoint I y
  disjoint .+ x
  disjoint .+ y
  disjoint .0. x
  disjoint .0. y
  disjoint V x
  disjoint V y
  disjoint G a
  disjoint G b
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint N a
  disjoint N b
  disjoint T a
  disjoint T b
  disjoint X a
  disjoint X b
  disjoint I a
  disjoint I b
  disjoint .+ a
  disjoint .+ b
  disjoint .0. a
  disjoint .0. b
  assert |- ( N : X --> RR -> ( T e. NrmGrp <-> ( G e. Grp /\ A. x e. X ( ( ( N ` x ) = 0 <-> x = .0. ) /\ ( N ` ( I ` x ) ) = ( N ` x ) /\ A. y e. X ( N ` ( x .+ y ) ) <_ ( ( N ` x ) + ( N ` y ) ) ) ) ) )

  proof
    cX
    cr
    cN
    wf
    #
    cT
    cngp
    wcel
    #
    cG
    cgrp
    wcel
    #
    vx
    cv
    #
    cN
    cfv
    #
    cc0
    wceq
    #
    @3
    c.0
    wceq
    #
    wb
    #
    @3
    cI
    cfv
    #
    cN
    cfv
    #
    @4
    wceq
    #
    @3
    vy
    cv
    #
    c.pl
    co
    #
    cN
    cfv
    #
    @4
    @11
    cN
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
    #
    w3a
    #
    vx
    cX
    wral
    #
    wa
    #
    @0
    cN
    cvv
    wcel
    #
    @1
    @20
    wi
    @0
    cX
    cvv
    wcel
    @21
    cX
    cG
    cbs
    cfv
    #
    cvv
    tngngp3.x
    cG
    cbs
    fvex
    eqeltri
    cX
    cr
    cvv
    cN
    fex
    mpan2
    @1
    @21
    @0
    @20
    @21
    @1
    @0
    @20
    wi
    #
    @21
    @1
    wa
    #
    @2
    @23
    cT
    cG
    cN
    cvv
    tngngp3.t
    tnggrpr
    @24
    @2
    @0
    @20
    @24
    @2
    @0
    w3a
    #
    @2
    @19
    @24
    @2
    @0
    simp2
    @25
    @19
    @3
    cT
    cnm
    cfv
    #
    cfv
    #
    cc0
    wceq
    #
    @3
    cT
    c0g
    cfv
    #
    wceq
    #
    wb
    #
    @3
    cT
    cminusg
    cfv
    #
    cfv
    #
    @26
    cfv
    #
    @27
    wceq
    #
    @3
    @11
    cT
    cplusg
    cfv
    #
    co
    #
    @26
    cfv
    #
    @27
    @11
    @26
    cfv
    #
    caddc
    co
    #
    cle
    wbr
    #
    vy
    cT
    cbs
    cfv
    #
    wral
    #
    w3a
    #
    vx
    @42
    wral
    #
    @24
    @2
    @45
    @0
    @1
    @45
    @21
    @1
    @44
    vx
    @42
    @1
    @3
    @42
    wcel
    #
    wa
    #
    @31
    @35
    @43
    @3
    cT
    @26
    @42
    @29
    @42
    eqid
    #
    @26
    eqid
    #
    @29
    eqid
    nmeq0
    @3
    cT
    @32
    @26
    @42
    @48
    @49
    @32
    eqid
    nminv
    @47
    @41
    vy
    @42
    @1
    @46
    @11
    @42
    wcel
    @41
    @3
    @11
    @36
    cT
    @26
    @42
    @48
    @49
    @36
    eqid
    nmtri
    3expa
    ralrimiva
    3jca
    ralrimiva
    adantl
    3ad2ant1
    @25
    cX
    @42
    wceq
    #
    c.pl
    @36
    wceq
    #
    cI
    @32
    wceq
    #
    w3a
    #
    cN
    @26
    wceq
    #
    c.0
    @29
    wceq
    #
    w3a
    #
    @19
    @45
    wb
    @25
    @53
    @54
    @55
    @24
    @2
    @53
    @0
    @21
    @53
    @1
    @21
    @50
    @51
    @52
    cX
    cT
    cG
    cN
    cvv
    tngngp3.t
    tngngp3.x
    tngbas
    c.pl
    cT
    cG
    cN
    cvv
    tngngp3.t
    tngngp3.p
    tngplusg
    @21
    cI
    cG
    cminusg
    cfv
    @32
    tngngp3.i
    @21
    vx
    vy
    @22
    cG
    cT
    @21
    @22
    eqidd
    @22
    cT
    cG
    cN
    cvv
    tngngp3.t
    @22
    eqid
    tngbas
    @21
    @3
    @11
    cG
    cplusg
    cfv
    #
    co
    @37
    wceq
    @3
    @22
    wcel
    @11
    @22
    wcel
    wa
    @21
    @57
    @36
    @3
    @11
    @57
    cT
    cG
    cN
    cvv
    tngngp3.t
    @57
    eqid
    tngplusg
    oveqd
    adantr
    grpinvpropd
    syl5eq
    3jca
    adantr
    3ad2ant1
    @2
    @0
    @54
    @24
    cr
    cT
    cG
    cN
    cX
    tngngp3.t
    tngngp3.x
    reex
    tngnm
    3adant1
    @24
    @2
    @55
    @0
    @21
    @55
    @1
    cT
    cG
    cN
    cvv
    c.0
    tngngp3.t
    tngngp3.z
    tng0
    adantr
    3ad2ant1
    3jca
    @56
    @18
    @44
    vx
    cX
    @42
    @53
    @54
    @50
    @55
    @50
    @51
    @52
    simp1
    3ad2ant1
    #
    @56
    @7
    @31
    @10
    @35
    @17
    @43
    @56
    @5
    @28
    @6
    @30
    @56
    @4
    @27
    cc0
    @56
    @3
    cN
    @26
    @53
    @54
    @55
    simp2
    #
    fveq1d
    #
    eqeq1d
    @56
    c.0
    @29
    @3
    @53
    @54
    @55
    simp3
    eqeq2d
    bibi12d
    @56
    @9
    @34
    @4
    @27
    @56
    @8
    @33
    cN
    @26
    @59
    @56
    @3
    cI
    @32
    @53
    @54
    @52
    @55
    @50
    @51
    @52
    simp3
    3ad2ant1
    fveq1d
    fveq12d
    @60
    eqeq12d
    @56
    @16
    @41
    vy
    cX
    @42
    @58
    @56
    @13
    @38
    @15
    @40
    cle
    @56
    @12
    @37
    cN
    @26
    @59
    @56
    c.pl
    @36
    @3
    @11
    @53
    @54
    @51
    @55
    @50
    @51
    @52
    simp2
    3ad2ant1
    oveqd
    fveq12d
    @54
    @53
    @15
    @40
    wceq
    @55
    @54
    @4
    @27
    @14
    @39
    caddc
    @3
    cN
    @26
    fveq1
    @11
    cN
    @26
    fveq1
    oveq12d
    3ad2ant2
    breq12d
    raleqbidv
    3anbi123d
    raleqbidv
    syl
    mpbird
    jca
    3exp
    mpd
    expcom
    com13
    mpd
    @0
    @20
    @1
    @0
    @20
    wa
    #
    va
    vb
    cT
    cG
    cG
    csg
    cfv
    #
    cN
    cX
    c.0
    tngngp3.t
    tngngp3.x
    @62
    eqid
    #
    tngngp3.z
    @20
    @2
    @0
    @2
    @19
    simpl
    adantl
    @0
    @20
    simpl
    @61
    va
    cv
    #
    cX
    wcel
    #
    @64
    cN
    cfv
    #
    cc0
    wceq
    #
    @64
    c.0
    wceq
    #
    wb
    #
    @20
    @65
    @69
    wi
    #
    @0
    @19
    @70
    @2
    @19
    @65
    @69
    @19
    @65
    wa
    @69
    @64
    cI
    cfv
    #
    cN
    cfv
    #
    @66
    wceq
    #
    @64
    @11
    c.pl
    co
    #
    cN
    cfv
    #
    @66
    @14
    caddc
    co
    #
    cle
    wbr
    #
    vy
    cX
    wral
    #
    w3a
    #
    @69
    @18
    @79
    vx
    @64
    cX
    vx
    va
    weq
    #
    @7
    @69
    @10
    @73
    @17
    @78
    @80
    @5
    @67
    @6
    @68
    @80
    @4
    @66
    cc0
    @3
    @64
    cN
    fveq2
    #
    eqeq1d
    @3
    @64
    c.0
    eqeq1
    bibi12d
    @80
    @9
    @72
    @4
    @66
    @80
    @8
    @71
    cN
    @3
    @64
    cI
    fveq2
    fveq2d
    @81
    eqeq12d
    @80
    @16
    @77
    vy
    cX
    @80
    @13
    @75
    @15
    @76
    cle
    @80
    @12
    @74
    cN
    @3
    @64
    @11
    c.pl
    oveq1
    fveq2d
    @80
    @4
    @66
    @14
    caddc
    @81
    oveq1d
    breq12d
    #
    ralbidv
    3anbi123d
    rspccva
    @69
    @73
    @78
    simp1
    syl
    ex
    adantl
    adantl
    imp
    @61
    @65
    vb
    cv
    #
    cX
    wcel
    #
    wa
    #
    wa
    #
    @64
    @83
    @62
    co
    #
    cN
    cfv
    @64
    @83
    cI
    cfv
    #
    c.pl
    co
    #
    cN
    cfv
    #
    @66
    @83
    cN
    cfv
    #
    caddc
    co
    #
    cle
    @86
    @87
    @89
    cN
    @85
    @87
    @89
    wceq
    @61
    cX
    c.pl
    cG
    cI
    @62
    @64
    @83
    tngngp3.x
    tngngp3.p
    tngngp3.i
    @63
    grpsubval
    adantl
    fveq2d
    @61
    @85
    @90
    @92
    cle
    wbr
    #
    @20
    @85
    @93
    wi
    #
    @0
    @19
    @2
    @94
    @19
    @10
    @17
    wa
    #
    vx
    cX
    wral
    #
    @2
    @94
    wi
    @18
    @95
    vx
    cX
    @7
    @10
    @17
    3simpc
    ralimi
    @96
    @2
    @94
    @96
    @2
    wa
    #
    @85
    @93
    @97
    @85
    wa
    #
    @90
    @66
    @88
    cN
    cfv
    #
    caddc
    co
    #
    @92
    cle
    @97
    @85
    @90
    @100
    cle
    wbr
    #
    @96
    @2
    @85
    @101
    wi
    #
    @96
    @17
    vx
    cX
    wral
    #
    @2
    @102
    wi
    @95
    @17
    vx
    cX
    @10
    @17
    simpr
    ralimi
    @103
    @2
    @85
    @101
    @65
    @88
    cX
    wcel
    #
    wa
    #
    @103
    @101
    @2
    @85
    wa
    @16
    @101
    @77
    vx
    vy
    @64
    @88
    cX
    cX
    @82
    @11
    @88
    wceq
    #
    @75
    @90
    @76
    @100
    cle
    @106
    @74
    @89
    cN
    @11
    @88
    @64
    c.pl
    oveq2
    fveq2d
    @106
    @14
    @99
    @66
    caddc
    @11
    @88
    cN
    fveq2
    oveq2d
    breq12d
    rspc2v
    @2
    @85
    @105
    @2
    @84
    @104
    @65
    @2
    @84
    @104
    cX
    cG
    cI
    @83
    tngngp3.x
    tngngp3.i
    grpinvcl
    ex
    anim2d
    imp
    syl11
    expd
    syl
    imp
    imp
    @98
    @91
    @99
    @66
    caddc
    @97
    @85
    @91
    @99
    wceq
    #
    @97
    @84
    @107
    @65
    @96
    @84
    @107
    wi
    #
    @2
    @96
    @10
    vx
    cX
    wral
    #
    @108
    @95
    @10
    vx
    cX
    @10
    @17
    simpl
    ralimi
    @109
    @84
    @107
    @109
    @84
    wa
    @99
    @91
    @10
    @99
    @91
    wceq
    vx
    @83
    cX
    vx
    vb
    weq
    #
    @9
    @99
    @4
    @91
    @110
    @8
    @88
    cN
    @3
    @83
    cI
    fveq2
    fveq2d
    @3
    @83
    cN
    fveq2
    eqeq12d
    rspccva
    eqcomd
    ex
    syl
    adantr
    adantld
    imp
    oveq2d
    breqtrrd
    ex
    ex
    syl
    impcom
    adantl
    imp
    eqbrtrd
    tngngpd
    ex
    impbid
end
