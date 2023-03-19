include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cgrp.mm"
include "csca.mm"
include "cfv.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "csn.mm"
include "cplusg.mm"
include "wceq.mm"
include "w3a.mm"
include "cmulr.mm"
include "cur.mm"
include "wral.mm"
include "cbs.mm"
include "clmod.mm"
include "cnx.mm"
include "cop.mm"
include "cpr.mm"
include "eqid.mm"
include "grp1.mm"
include "cvv.mm"
include "fvex.mm"
include "cmpt2.mm"
include "ctp.mm"
include "cun.mm"
include "snex.mm"
include "grpbase.mm"
include "ax-mp.mm"
include "opeq2i.mm"
include "tpeq1.mm"
include "uneq1i.mm"
include "eqtri.mm"
include "lmodbase.mm"
include "eqcomi.mm"
include "grpplusg.mm"
include "tpeq2.mm"
include "lmodplusg.mm"
include "grpprop.mm"
include "sylibr.mm"
include "adantr.mm"
include "lmodsca.mm"
include "eqcomd.mm"
include "adantl.mm"
include "simpr.mm"
include "eqeltrd.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "simpll.mm"
include "simplr.mm"
include "simprr.mm"
include "3jca.mm"
include "lmod1lem1.mm"
include "syl.mm"
include "lmod1lem2.mm"
include "lmod1lem3.mm"
include "lmod1lem4.mm"
include "lmod1lem5.mm"
include "jca32.mm"
include "ex.mm"
include "sylbid.mm"
include "ralrimivv.mm"
include "wb.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "3anbi2d.mm"
include "anbi1d.mm"
include "ralbidv.mm"
include "ralsng.mm"
include "eleq1d.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "3anbi123d.mm"
include "id.mm"
include "bitrd.mm"
include "2ralbidv.mm"
include "mpbird.mm"
include "islmod.mm"
include "syl3anbrc.mm"

theorem lmod1
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cI: class I
  let cM: class M
  let cV: class V
  let vr: setvar r
  let vq: setvar q
  let vw: setvar w
  let vk: setvar k
  assume lmod1.m: |- M = ( { <. ( Base ` ndx ) , { I } >. , <. ( +g ` ndx ) , { <. <. I , I >. , I >. } >. , <. ( Scalar ` ndx ) , R >. } u. { <. ( .s ` ndx ) , ( x e. ( Base ` R ) , y e. { I } |-> y ) >. } )

  disjoint I x
  disjoint I y
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint V x
  disjoint V y
  disjoint M x
  disjoint M y
  disjoint I r
  disjoint r x
  disjoint r y
  disjoint R r
  disjoint V r
  disjoint I q
  disjoint R q
  disjoint V q
  disjoint q x
  disjoint q y
  disjoint I w
  disjoint w x
  disjoint M r
  disjoint M q
  disjoint M w
  disjoint q r
  disjoint r w
  disjoint q w
  disjoint k x
  assert |- ( ( I e. V /\ R e. Ring ) -> M e. LMod )

  proof
    cI
    cV
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    cM
    cgrp
    wcel
    #
    cM
    csca
    cfv
    #
    crg
    wcel
    vr
    cv
    #
    vw
    cv
    #
    cM
    cvsca
    cfv
    #
    co
    #
    cI
    csn
    #
    wcel
    #
    @5
    @6
    vx
    cv
    #
    cM
    cplusg
    cfv
    #
    co
    #
    @7
    co
    #
    @8
    @5
    @11
    @7
    co
    #
    @12
    co
    #
    wceq
    #
    vq
    cv
    #
    @5
    @4
    cplusg
    cfv
    #
    co
    #
    @6
    @7
    co
    #
    @18
    @6
    @7
    co
    #
    @8
    @12
    co
    #
    wceq
    #
    w3a
    #
    @18
    @5
    @4
    cmulr
    cfv
    #
    co
    #
    @6
    @7
    co
    #
    @18
    @8
    @7
    co
    #
    wceq
    #
    @4
    cur
    cfv
    #
    @6
    @7
    co
    #
    @6
    wceq
    #
    wa
    #
    wa
    #
    vw
    @9
    wral
    #
    vx
    @9
    wral
    #
    vr
    @4
    cbs
    cfv
    #
    wral
    vq
    @38
    wral
    #
    cM
    clmod
    wcel
    @0
    @3
    @1
    @0
    cnx
    cbs
    cfv
    #
    @9
    cop
    #
    cnx
    cplusg
    cfv
    #
    cI
    cI
    cop
    cI
    cop
    #
    csn
    #
    cop
    #
    cpr
    #
    cgrp
    wcel
    @3
    cI
    @46
    cV
    @46
    eqid
    #
    grp1
    cM
    @46
    @46
    cbs
    cfv
    #
    cM
    cbs
    cfv
    #
    @48
    cvv
    wcel
    @48
    @49
    wceq
    @46
    cbs
    fvex
    @48
    @44
    vx
    vy
    cR
    cbs
    cfv
    #
    @9
    vy
    cv
    cmpt2
    #
    cR
    cM
    cvv
    cM
    @41
    @45
    cnx
    csca
    cfv
    cR
    cop
    #
    ctp
    #
    cnx
    cvsca
    cfv
    @51
    cop
    csn
    #
    cun
    #
    @40
    @48
    cop
    #
    @45
    @52
    ctp
    #
    @54
    cun
    lmod1.m
    @53
    @57
    @54
    @41
    @56
    wceq
    @53
    @57
    wceq
    @9
    @48
    @40
    @9
    cvv
    wcel
    #
    @9
    @48
    wceq
    cI
    snex
    #
    @9
    @44
    @46
    cvv
    @47
    grpbase
    ax-mp
    opeq2i
    @41
    @56
    @45
    @52
    tpeq1
    ax-mp
    uneq1i
    eqtri
    lmodbase
    ax-mp
    eqcomi
    @46
    cplusg
    cfv
    #
    @12
    @60
    cvv
    wcel
    @60
    @12
    wceq
    @46
    cplusg
    fvex
    @9
    @60
    @51
    cR
    cM
    cvv
    cM
    @55
    @41
    @42
    @60
    cop
    #
    @52
    ctp
    #
    @54
    cun
    lmod1.m
    @53
    @62
    @54
    @45
    @61
    wceq
    @53
    @62
    wceq
    @44
    @60
    @42
    @44
    cvv
    wcel
    @44
    @60
    wceq
    @43
    snex
    @9
    @44
    @46
    cvv
    @47
    grpplusg
    ax-mp
    opeq2i
    @45
    @61
    @41
    @52
    tpeq2
    ax-mp
    uneq1i
    eqtri
    lmodplusg
    ax-mp
    eqcomi
    grpprop
    sylibr
    adantr
    @2
    @4
    cR
    crg
    @1
    @4
    cR
    wceq
    @0
    @1
    cR
    @4
    @9
    @44
    @51
    cR
    cM
    crg
    lmod1.m
    lmodsca
    eqcomd
    adantl
    #
    @0
    @1
    simpr
    eqeltrd
    @2
    @39
    @5
    cI
    @7
    co
    #
    @9
    wcel
    #
    @5
    cI
    cI
    @12
    co
    #
    @7
    co
    #
    @64
    @64
    @12
    co
    #
    wceq
    #
    @20
    cI
    @7
    co
    #
    @18
    cI
    @7
    co
    #
    @64
    @12
    co
    #
    wceq
    #
    w3a
    #
    @27
    cI
    @7
    co
    #
    @18
    @64
    @7
    co
    #
    wceq
    #
    @31
    cI
    @7
    co
    #
    cI
    wceq
    #
    wa
    #
    wa
    #
    vr
    @38
    wral
    vq
    @38
    wral
    @2
    @81
    vq
    vr
    @38
    @38
    @2
    @18
    @38
    wcel
    #
    @5
    @38
    wcel
    #
    wa
    @18
    @50
    wcel
    #
    @5
    @50
    wcel
    #
    wa
    #
    @81
    @2
    @82
    @84
    @83
    @85
    @2
    @38
    @50
    @18
    @2
    @4
    cR
    cbs
    @63
    fveq2d
    #
    eleq2d
    @2
    @38
    @50
    @5
    @87
    eleq2d
    anbi12d
    @2
    @86
    @81
    @2
    @86
    wa
    #
    @74
    @77
    @79
    @88
    @65
    @69
    @73
    @88
    @0
    @1
    @85
    w3a
    #
    @65
    @88
    @0
    @1
    @85
    @0
    @1
    @86
    simpll
    @0
    @1
    @86
    simplr
    @2
    @84
    @85
    simprr
    3jca
    #
    vx
    vy
    cR
    cI
    cM
    cV
    vr
    lmod1.m
    lmod1lem1
    syl
    @88
    @89
    @69
    @90
    vx
    vy
    cR
    cI
    cM
    cV
    vr
    lmod1.m
    lmod1lem2
    syl
    vx
    vy
    cR
    cI
    cM
    cV
    vr
    vq
    lmod1.m
    lmod1lem3
    3jca
    vx
    vy
    cR
    cI
    cM
    cV
    vr
    vq
    lmod1.m
    lmod1lem4
    @2
    @79
    @86
    vx
    vy
    cR
    cI
    cM
    cV
    lmod1.m
    lmod1lem5
    adantr
    jca32
    ex
    sylbid
    ralrimivv
    @2
    @37
    @81
    vq
    vr
    @38
    @38
    @2
    @37
    @10
    @5
    @6
    cI
    @12
    co
    #
    @7
    co
    #
    @8
    @64
    @12
    co
    #
    wceq
    #
    @24
    w3a
    #
    @34
    wa
    #
    vw
    @9
    wral
    #
    @81
    @0
    @37
    @97
    wb
    @1
    @36
    @97
    vx
    cI
    cV
    @11
    cI
    wceq
    #
    @35
    @96
    vw
    @9
    @98
    @25
    @95
    @34
    @98
    @17
    @94
    @10
    @24
    @98
    @14
    @92
    @16
    @93
    @98
    @13
    @91
    @5
    @7
    @11
    cI
    @6
    @12
    oveq2
    oveq2d
    @98
    @15
    @64
    @8
    @12
    @11
    cI
    @5
    @7
    oveq2
    oveq2d
    eqeq12d
    3anbi2d
    anbi1d
    ralbidv
    ralsng
    adantr
    @0
    @97
    @81
    wb
    @1
    @96
    @81
    vw
    cI
    cV
    @6
    cI
    wceq
    #
    @95
    @74
    @34
    @80
    @99
    @10
    @65
    @94
    @69
    @24
    @73
    @99
    @8
    @64
    @9
    @6
    cI
    @5
    @7
    oveq2
    #
    eleq1d
    @99
    @92
    @67
    @93
    @68
    @99
    @91
    @66
    @5
    @7
    @6
    cI
    cI
    @12
    oveq1
    oveq2d
    @99
    @8
    @64
    @64
    @12
    @100
    oveq1d
    eqeq12d
    @99
    @21
    @70
    @23
    @72
    @6
    cI
    @20
    @7
    oveq2
    @99
    @22
    @71
    @8
    @64
    @12
    @6
    cI
    @18
    @7
    oveq2
    @100
    oveq12d
    eqeq12d
    3anbi123d
    @99
    @30
    @77
    @33
    @79
    @99
    @28
    @75
    @29
    @76
    @6
    cI
    @27
    @7
    oveq2
    @99
    @8
    @64
    @18
    @7
    @100
    oveq2d
    eqeq12d
    @99
    @32
    @78
    @6
    cI
    @6
    cI
    @31
    @7
    oveq2
    @99
    id
    eqeq12d
    anbi12d
    anbi12d
    ralsng
    adantr
    bitrd
    2ralbidv
    mpbird
    vx
    vw
    @12
    @19
    @7
    @26
    @31
    @4
    @38
    @9
    cM
    vr
    vq
    @58
    @9
    @49
    wceq
    @59
    @9
    @44
    @51
    cR
    cM
    cvv
    lmod1.m
    lmodbase
    ax-mp
    @12
    eqid
    @7
    eqid
    @4
    eqid
    @38
    eqid
    @19
    eqid
    @26
    eqid
    @31
    eqid
    islmod
    syl3anbrc
end
