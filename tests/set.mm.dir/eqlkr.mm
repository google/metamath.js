include "clvec.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "wrex.mm"
include "c0g.mm"
include "csn.mm"
include "cxp.mm"
include "cur.mm"
include "crg.mm"
include "simpl1.mm"
include "clmod.mm"
include "lveclmod.mm"
include "lmodring.mm"
include "syl.mm"
include "eqid.mm"
include "ringidcl.mm"
include "simp11.mm"
include "simp12l.mm"
include "simp3.mm"
include "lflcl.mm"
include "syl3anc.mm"
include "ringridm.mm"
include "syl2anc.mm"
include "simp2.mm"
include "simp13.mm"
include "wb.mm"
include "lkr0f.mm"
include "mpbird.mm"
include "eqtr3d.mm"
include "simp12r.mm"
include "mpbid.mm"
include "eqtr4d.mm"
include "fveq1d.mm"
include "eqtr2d.mm"
include "3expia.mm"
include "ralrimiv.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "wne.mm"
include "simpl2l.mm"
include "simpr.mm"
include "lfl1.mm"
include "wi.mm"
include "simpl2r.mm"
include "simpr2.mm"
include "csg.mm"
include "cvsca.mm"
include "simp22.mm"
include "lflmul.mm"
include "syl112anc.mm"
include "oveq2d.mm"
include "lmodvscl.mm"
include "lflsub.mm"
include "lmodvsubcl.mm"
include "simp23.mm"
include "3eqtrd.mm"
include "cgrp.mm"
include "lmodfgrp.mm"
include "grpsubid.mm"
include "ellkr.mm"
include "mpbir2and.mm"
include "eleqtrd.mm"
include "simprd.mm"
include "3adant3.mm"
include "lmodmcl.mm"
include "grpsubeq0.mm"
include "3exp2.mm"
include "imp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "pm2.61dane.mm"

theorem eqlkr
  let vx: setvar x
  let cD: class D
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let cV: class V
  let cW: class W
  let vr: setvar r
  let vz: setvar z
  assume eqlkr.d: |- D = ( Scalar ` W )
  assume eqlkr.k: |- K = ( Base ` D )
  assume eqlkr.t: |- .x. = ( .r ` D )
  assume eqlkr.v: |- V = ( Base ` W )
  assume eqlkr.f: |- F = ( LFnl ` W )
  assume eqlkr.l: |- L = ( LKer ` W )

  disjoint r x
  disjoint D r
  disjoint D x
  disjoint F x
  disjoint G r
  disjoint G x
  disjoint H r
  disjoint H x
  disjoint V r
  disjoint V x
  disjoint K r
  disjoint L x
  disjoint .x. r
  disjoint W x
  disjoint r z
  disjoint x z
  disjoint D z
  disjoint F z
  disjoint G z
  disjoint H z
  disjoint V z
  disjoint K z
  disjoint L z
  disjoint .x. z
  disjoint W z
  assert |- ( ( W e. LVec /\ ( G e. F /\ H e. F ) /\ ( L ` G ) = ( L ` H ) ) -> E. r e. K A. x e. V ( H ` x ) = ( ( G ` x ) .x. r ) )

  proof
    cW
    clvec
    wcel
    #
    cG
    cF
    wcel
    #
    cH
    cF
    wcel
    #
    wa
    #
    cG
    cL
    cfv
    #
    cH
    cL
    cfv
    #
    wceq
    #
    w3a
    #
    vx
    cv
    #
    cH
    cfv
    #
    @8
    cG
    cfv
    #
    vr
    cv
    #
    c.x
    co
    #
    wceq
    #
    vx
    cV
    wral
    #
    vr
    cK
    wrex
    #
    cG
    cV
    cD
    c0g
    cfv
    #
    csn
    cxp
    #
    @7
    cG
    @17
    wceq
    #
    wa
    #
    cD
    cur
    cfv
    #
    cK
    wcel
    #
    @9
    @10
    @20
    c.x
    co
    #
    wceq
    #
    vx
    cV
    wral
    #
    @15
    @19
    cD
    crg
    wcel
    #
    @21
    @19
    @0
    @25
    @0
    @3
    @6
    @18
    simpl1
    @0
    cW
    clmod
    wcel
    #
    @25
    cW
    lveclmod
    #
    cD
    cW
    eqlkr.d
    lmodring
    syl
    #
    syl
    cK
    cD
    @20
    eqlkr.k
    @20
    eqid
    #
    ringidcl
    syl
    @19
    @23
    vx
    cV
    @7
    @18
    @8
    cV
    wcel
    #
    @23
    @7
    @18
    @30
    w3a
    #
    @22
    @10
    @9
    @31
    @25
    @10
    cK
    wcel
    #
    @22
    @10
    wceq
    #
    @31
    @0
    @25
    @0
    @3
    @6
    @18
    @30
    simp11
    #
    @28
    syl
    @31
    @0
    @1
    @30
    @32
    @34
    @1
    @2
    @0
    @6
    @18
    @30
    simp12l
    #
    @7
    @18
    @30
    simp3
    cD
    cF
    cG
    cK
    cV
    cW
    @8
    clvec
    eqlkr.d
    eqlkr.k
    eqlkr.v
    eqlkr.f
    lflcl
    #
    syl3anc
    cK
    cD
    c.x
    @20
    @10
    eqlkr.k
    eqlkr.t
    @29
    ringridm
    #
    syl2anc
    @31
    @8
    cG
    cH
    @31
    cG
    @17
    cH
    @7
    @18
    @30
    simp2
    #
    @31
    @5
    cV
    wceq
    #
    cH
    @17
    wceq
    #
    @31
    @4
    @5
    cV
    @0
    @3
    @6
    @18
    @30
    simp13
    @31
    @4
    cV
    wceq
    #
    @18
    @38
    @31
    @26
    @1
    @41
    @18
    wb
    @31
    @0
    @26
    @34
    @27
    syl
    #
    @35
    cD
    cF
    cG
    cL
    cV
    cW
    @16
    eqlkr.d
    @16
    eqid
    #
    eqlkr.v
    eqlkr.f
    eqlkr.l
    lkr0f
    syl2anc
    mpbird
    eqtr3d
    @31
    @26
    @2
    @39
    @40
    wb
    @42
    @1
    @2
    @0
    @6
    @18
    @30
    simp12r
    cD
    cF
    cH
    cL
    cV
    cW
    @16
    eqlkr.d
    @43
    eqlkr.v
    eqlkr.f
    eqlkr.l
    lkr0f
    syl2anc
    mpbid
    eqtr4d
    fveq1d
    eqtr2d
    3expia
    ralrimiv
    @14
    @24
    vr
    @20
    cK
    @11
    @20
    wceq
    #
    @13
    @23
    vx
    cV
    @44
    @12
    @22
    @9
    @11
    @20
    @10
    c.x
    oveq2
    eqeq2d
    ralbidv
    rspcev
    syl2anc
    @7
    cG
    @17
    wne
    #
    wa
    #
    vz
    cv
    #
    cG
    cfv
    #
    @20
    wceq
    #
    vz
    cV
    wrex
    #
    @15
    @46
    @0
    @1
    @45
    @50
    @0
    @3
    @6
    @45
    simpl1
    @1
    @2
    @0
    @6
    @45
    simpl2l
    @7
    @45
    simpr
    vz
    cD
    @20
    cF
    cG
    cV
    cW
    @16
    eqlkr.d
    @43
    @29
    eqlkr.v
    eqlkr.f
    lfl1
    syl3anc
    @46
    @49
    @15
    vz
    cV
    @7
    @45
    @47
    cV
    wcel
    #
    @49
    @15
    wi
    wi
    @7
    @45
    @51
    @49
    @15
    @7
    @45
    @51
    @49
    w3a
    #
    wa
    #
    @47
    cH
    cfv
    #
    cK
    wcel
    #
    @9
    @10
    @54
    c.x
    co
    #
    wceq
    #
    vx
    cV
    wral
    #
    @15
    @53
    @0
    @2
    @51
    @55
    @0
    @3
    @6
    @52
    simpl1
    @1
    @2
    @0
    @6
    @52
    simpl2r
    @7
    @45
    @51
    @49
    simpr2
    cD
    cF
    cH
    cK
    cV
    cW
    @47
    clvec
    eqlkr.d
    eqlkr.k
    eqlkr.v
    eqlkr.f
    lflcl
    syl3anc
    #
    @53
    @57
    vx
    cV
    @7
    @52
    @30
    @57
    @7
    @52
    @30
    w3a
    #
    @9
    @56
    cD
    csg
    cfv
    #
    co
    #
    @16
    wceq
    #
    @57
    @60
    @9
    @10
    @47
    cW
    cvsca
    cfv
    #
    co
    #
    cH
    cfv
    #
    @61
    co
    #
    @62
    @16
    @60
    @66
    @56
    @9
    @61
    @60
    @26
    @2
    @32
    @51
    @66
    @56
    wceq
    @60
    @0
    @26
    @0
    @3
    @6
    @52
    @30
    simp11
    #
    @27
    syl
    #
    @1
    @2
    @0
    @6
    @52
    @30
    simp12r
    #
    @60
    @26
    @1
    @30
    @32
    @69
    @1
    @2
    @0
    @6
    @52
    @30
    simp12l
    #
    @7
    @52
    @30
    simp3
    #
    cD
    cF
    cG
    cK
    cV
    cW
    @8
    clmod
    eqlkr.d
    eqlkr.k
    eqlkr.v
    eqlkr.f
    lflcl
    syl3anc
    #
    @7
    @45
    @51
    @49
    @30
    simp22
    #
    cD
    @10
    @64
    c.x
    cF
    cH
    cK
    cV
    cW
    @47
    eqlkr.d
    eqlkr.k
    eqlkr.t
    eqlkr.v
    @64
    eqid
    #
    eqlkr.f
    lflmul
    syl112anc
    oveq2d
    @60
    @8
    @65
    cW
    csg
    cfv
    #
    co
    #
    cH
    cfv
    #
    @67
    @16
    @60
    @26
    @2
    @30
    @65
    cV
    wcel
    #
    @78
    @67
    wceq
    @69
    @70
    @72
    @60
    @26
    @32
    @51
    @79
    @69
    @73
    @74
    @10
    @64
    cD
    cK
    cV
    cW
    @47
    eqlkr.v
    eqlkr.d
    @75
    eqlkr.k
    lmodvscl
    syl3anc
    #
    cD
    cF
    cH
    @61
    @76
    cV
    cW
    @8
    @65
    eqlkr.d
    @61
    eqid
    #
    eqlkr.v
    @76
    eqid
    #
    eqlkr.f
    lflsub
    syl112anc
    @60
    @77
    cV
    wcel
    #
    @78
    @16
    wceq
    #
    @60
    @77
    @5
    wcel
    #
    @83
    @84
    wa
    #
    @60
    @77
    @4
    @5
    @60
    @77
    @4
    wcel
    #
    @83
    @77
    cG
    cfv
    #
    @16
    wceq
    #
    @60
    @26
    @30
    @79
    @83
    @69
    @72
    @80
    @76
    cV
    cW
    @8
    @65
    eqlkr.v
    @82
    lmodvsubcl
    syl3anc
    @60
    @88
    @10
    @65
    cG
    cfv
    #
    @61
    co
    #
    @10
    @10
    @61
    co
    #
    @16
    @60
    @26
    @1
    @30
    @79
    @88
    @91
    wceq
    @69
    @71
    @72
    @80
    cD
    cF
    cG
    @61
    @76
    cV
    cW
    @8
    @65
    eqlkr.d
    @81
    eqlkr.v
    @82
    eqlkr.f
    lflsub
    syl112anc
    @60
    @90
    @10
    @10
    @61
    @60
    @90
    @10
    @48
    c.x
    co
    #
    @22
    @10
    @60
    @26
    @1
    @32
    @51
    @90
    @93
    wceq
    @69
    @71
    @60
    @0
    @1
    @30
    @32
    @68
    @71
    @72
    @36
    syl3anc
    #
    @74
    cD
    @10
    @64
    c.x
    cF
    cG
    cK
    cV
    cW
    @47
    eqlkr.d
    eqlkr.k
    eqlkr.t
    eqlkr.v
    @75
    eqlkr.f
    lflmul
    syl112anc
    @60
    @48
    @20
    @10
    c.x
    @7
    @45
    @51
    @49
    @30
    simp23
    oveq2d
    @60
    @25
    @32
    @33
    @60
    @0
    @25
    @68
    @28
    syl
    @94
    @37
    syl2anc
    3eqtrd
    oveq2d
    @60
    cD
    cgrp
    wcel
    #
    @32
    @92
    @16
    wceq
    @60
    @0
    @95
    @68
    @0
    @26
    @95
    @27
    cD
    cW
    eqlkr.d
    lmodfgrp
    syl
    syl
    #
    @94
    cK
    cD
    @61
    @10
    @16
    eqlkr.k
    @43
    @81
    grpsubid
    syl2anc
    3eqtrd
    @60
    @0
    @1
    @87
    @83
    @89
    wa
    wb
    @68
    @71
    cD
    cF
    cG
    cL
    cV
    cW
    @77
    clvec
    @16
    eqlkr.v
    eqlkr.d
    @43
    eqlkr.f
    eqlkr.l
    ellkr
    syl2anc
    mpbir2and
    @0
    @3
    @6
    @52
    @30
    simp13
    eleqtrd
    @60
    @0
    @2
    @85
    @86
    wb
    @68
    @70
    cD
    cF
    cH
    cL
    cV
    cW
    @77
    clvec
    @16
    eqlkr.v
    eqlkr.d
    @43
    eqlkr.f
    eqlkr.l
    ellkr
    syl2anc
    mpbid
    simprd
    eqtr3d
    eqtr3d
    @60
    @95
    @9
    cK
    wcel
    #
    @56
    cK
    wcel
    #
    @63
    @57
    wb
    @96
    @60
    @0
    @2
    @30
    @97
    @68
    @70
    @72
    cD
    cF
    cH
    cK
    cV
    cW
    @8
    clvec
    eqlkr.d
    eqlkr.k
    eqlkr.v
    eqlkr.f
    lflcl
    syl3anc
    @60
    @26
    @32
    @55
    @98
    @69
    @94
    @7
    @52
    @55
    @30
    @59
    3adant3
    c.x
    cD
    cK
    cW
    @10
    @54
    eqlkr.d
    eqlkr.k
    eqlkr.t
    lmodmcl
    syl3anc
    cK
    cD
    @61
    @9
    @56
    @16
    eqlkr.k
    @43
    @81
    grpsubeq0
    syl3anc
    mpbid
    3expia
    ralrimiv
    @14
    @58
    vr
    @54
    cK
    @11
    @54
    wceq
    #
    @13
    @57
    vx
    cV
    @99
    @12
    @56
    @9
    @11
    @54
    @10
    c.x
    oveq2
    eqeq2d
    ralbidv
    rspcev
    syl2anc
    3exp2
    imp
    rexlimdv
    mpd
    pm2.61dane
end
