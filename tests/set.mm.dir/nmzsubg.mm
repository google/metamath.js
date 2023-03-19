include "cgrp.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "cminusg.mm"
include "wa.mm"
include "wb.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "a1i.mm"
include "c0g.mm"
include "eqid.mm"
include "grpidcl.mm"
include "grplid.mm"
include "grprid.mm"
include "eqtr4d.mm"
include "eleq1d.mm"
include "ralrimiva.mm"
include "elnmz.mm"
include "sylanbrc.mm"
include "ne0i.mm"
include "syl.mm"
include "w3a.mm"
include "id.mm"
include "sseli.mm"
include "grpcl.mm"
include "syl3an.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl2.mm"
include "sseldi.mm"
include "simpl3.mm"
include "simpr.mm"
include "grpass.mm"
include "syl13anc.mm"
include "syl3anc.mm"
include "nmzbi.mm"
include "syl2anc.mm"
include "3bitrd.mm"
include "3expa.mm"
include "grpinvcl.mm"
include "sylan2.mm"
include "simplr.mm"
include "simpll.mm"
include "adantr.mm"
include "grprinv.mm"
include "oveq1d.mm"
include "3eqtr3d.mm"
include "grplinv.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "eqtrd.mm"
include "3bitr3rd.mm"
include "jca.mm"
include "issubg2.mm"
include "mpbir3and.mm"

theorem nmzsubg
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let cS: class S
  let cG: class G
  let cN: class N
  let cX: class X
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vu: setvar u
  let vw: setvar w
  let cH: class H
  assume elnmz.1: |- N = { x e. X | A. y e. X ( ( x .+ y ) e. S <-> ( y .+ x ) e. S ) }
  assume nmzsubg.2: |- X = ( Base ` G )
  assume nmzsubg.3: |- .+ = ( +g ` G )

  disjoint x y
  disjoint G x
  disjoint G y
  disjoint S x
  disjoint S y
  disjoint .+ x
  disjoint .+ y
  disjoint X x
  disjoint X y
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint B z
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint G u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint G w
  disjoint y z
  disjoint G z
  disjoint N u
  disjoint N w
  disjoint N z
  disjoint S u
  disjoint S w
  disjoint S z
  disjoint .+ u
  disjoint .+ w
  disjoint .+ z
  disjoint H w
  disjoint H z
  disjoint X u
  disjoint X w
  disjoint X z
  assert |- ( G e. Grp -> N e. ( SubGrp ` G ) )

  proof
    cG
    cgrp
    wcel
    #
    cN
    cG
    csubg
    cfv
    wcel
    cN
    cX
    wss
    #
    cN
    c0
    wne
    #
    vz
    cv
    #
    vw
    cv
    #
    c.pl
    co
    #
    cN
    wcel
    #
    vw
    cN
    wral
    #
    @3
    cG
    cminusg
    cfv
    #
    cfv
    #
    cN
    wcel
    #
    wa
    #
    vz
    cN
    wral
    @1
    @0
    cN
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    cS
    wcel
    @13
    @12
    c.pl
    co
    cS
    wcel
    wb
    vy
    cX
    wral
    #
    vx
    cX
    crab
    cX
    elnmz.1
    @14
    vx
    cX
    ssrab2
    eqsstri
    #
    a1i
    @0
    cG
    c0g
    cfv
    #
    cN
    wcel
    #
    @2
    @0
    @16
    cX
    wcel
    @16
    @3
    c.pl
    co
    #
    cS
    wcel
    @3
    @16
    c.pl
    co
    #
    cS
    wcel
    wb
    #
    vz
    cX
    wral
    @17
    cX
    cG
    @16
    nmzsubg.2
    @16
    eqid
    #
    grpidcl
    @0
    @20
    vz
    cX
    @0
    @3
    cX
    wcel
    #
    wa
    #
    @18
    @19
    cS
    @23
    @18
    @3
    @19
    cX
    c.pl
    cG
    @3
    @16
    nmzsubg.2
    nmzsubg.3
    @21
    grplid
    cX
    c.pl
    cG
    @3
    @16
    nmzsubg.2
    nmzsubg.3
    @21
    grprid
    eqtr4d
    eleq1d
    ralrimiva
    vx
    vy
    vz
    @16
    c.pl
    cS
    cN
    cX
    elnmz.1
    elnmz
    sylanbrc
    cN
    @16
    ne0i
    syl
    @0
    @11
    vz
    cN
    @0
    @3
    cN
    wcel
    #
    wa
    #
    @7
    @10
    @25
    @6
    vw
    cN
    @0
    @24
    @4
    cN
    wcel
    #
    @6
    @0
    @24
    @26
    w3a
    #
    @5
    cX
    wcel
    #
    @5
    vu
    cv
    #
    c.pl
    co
    #
    cS
    wcel
    #
    @29
    @5
    c.pl
    co
    #
    cS
    wcel
    #
    wb
    #
    vu
    cX
    wral
    @6
    @0
    @0
    @24
    @22
    @26
    @4
    cX
    wcel
    #
    @28
    @0
    id
    cN
    cX
    @3
    @15
    sseli
    #
    cN
    cX
    @4
    @15
    sseli
    cX
    c.pl
    cG
    @3
    @4
    nmzsubg.2
    nmzsubg.3
    grpcl
    syl3an
    @27
    @34
    vu
    cX
    @27
    @29
    cX
    wcel
    #
    wa
    #
    @31
    @3
    @4
    @29
    c.pl
    co
    #
    c.pl
    co
    #
    cS
    wcel
    #
    @29
    @3
    c.pl
    co
    #
    @4
    c.pl
    co
    #
    cS
    wcel
    #
    @33
    @38
    @30
    @40
    cS
    @38
    @0
    @22
    @35
    @37
    @30
    @40
    wceq
    @0
    @24
    @26
    @37
    simpl1
    #
    @38
    cN
    cX
    @3
    @15
    @0
    @24
    @26
    @37
    simpl2
    #
    sseldi
    #
    @38
    cN
    cX
    @4
    @15
    @0
    @24
    @26
    @37
    simpl3
    #
    sseldi
    #
    @27
    @37
    simpr
    #
    cX
    c.pl
    cG
    @3
    @4
    @29
    nmzsubg.2
    nmzsubg.3
    grpass
    syl13anc
    eleq1d
    @38
    @41
    @39
    @3
    c.pl
    co
    #
    cS
    wcel
    #
    @4
    @42
    c.pl
    co
    #
    cS
    wcel
    #
    @44
    @38
    @24
    @39
    cX
    wcel
    #
    @41
    @52
    wb
    @46
    @38
    @0
    @35
    @37
    @55
    @45
    @49
    @50
    cX
    c.pl
    cG
    @4
    @29
    nmzsubg.2
    nmzsubg.3
    grpcl
    syl3anc
    vx
    vy
    @3
    @39
    c.pl
    cS
    cN
    cX
    elnmz.1
    nmzbi
    syl2anc
    @38
    @51
    @53
    cS
    @38
    @0
    @35
    @37
    @22
    @51
    @53
    wceq
    @45
    @49
    @50
    @47
    cX
    c.pl
    cG
    @4
    @29
    @3
    nmzsubg.2
    nmzsubg.3
    grpass
    syl13anc
    eleq1d
    @38
    @26
    @42
    cX
    wcel
    #
    @54
    @44
    wb
    @48
    @38
    @0
    @37
    @22
    @56
    @45
    @50
    @47
    cX
    c.pl
    cG
    @29
    @3
    nmzsubg.2
    nmzsubg.3
    grpcl
    syl3anc
    vx
    vy
    @4
    @42
    c.pl
    cS
    cN
    cX
    elnmz.1
    nmzbi
    syl2anc
    3bitrd
    @38
    @43
    @32
    cS
    @38
    @0
    @37
    @22
    @35
    @43
    @32
    wceq
    @45
    @50
    @47
    @49
    cX
    c.pl
    cG
    @29
    @3
    @4
    nmzsubg.2
    nmzsubg.3
    grpass
    syl13anc
    eleq1d
    3bitrd
    ralrimiva
    vx
    vy
    vu
    @5
    c.pl
    cS
    cN
    cX
    elnmz.1
    elnmz
    sylanbrc
    3expa
    ralrimiva
    @25
    @9
    cX
    wcel
    #
    @9
    @29
    c.pl
    co
    #
    cS
    wcel
    #
    @29
    @9
    c.pl
    co
    #
    cS
    wcel
    #
    wb
    #
    vu
    cX
    wral
    @10
    @24
    @0
    @22
    @57
    @36
    cX
    cG
    @8
    @3
    nmzsubg.2
    @8
    eqid
    #
    grpinvcl
    sylan2
    #
    @25
    @62
    vu
    cX
    @25
    @37
    wa
    #
    @3
    @9
    @60
    c.pl
    co
    #
    c.pl
    co
    #
    cS
    wcel
    #
    @66
    @3
    c.pl
    co
    #
    cS
    wcel
    #
    @61
    @59
    @65
    @24
    @66
    cX
    wcel
    #
    @68
    @70
    wb
    @0
    @24
    @37
    simplr
    #
    @65
    @0
    @57
    @60
    cX
    wcel
    #
    @71
    @0
    @24
    @37
    simpll
    #
    @25
    @57
    @37
    @64
    adantr
    #
    @65
    @0
    @37
    @57
    @73
    @74
    @25
    @37
    simpr
    #
    @75
    cX
    c.pl
    cG
    @29
    @9
    nmzsubg.2
    nmzsubg.3
    grpcl
    syl3anc
    #
    cX
    c.pl
    cG
    @9
    @60
    nmzsubg.2
    nmzsubg.3
    grpcl
    syl3anc
    vx
    vy
    @3
    @66
    c.pl
    cS
    cN
    cX
    elnmz.1
    nmzbi
    syl2anc
    @65
    @67
    @60
    cS
    @65
    @3
    @9
    c.pl
    co
    #
    @60
    c.pl
    co
    #
    @16
    @60
    c.pl
    co
    #
    @67
    @60
    @65
    @78
    @16
    @60
    c.pl
    @65
    @0
    @22
    @78
    @16
    wceq
    @74
    @65
    cN
    cX
    @3
    @15
    @72
    sseldi
    #
    cX
    c.pl
    cG
    @8
    @3
    @16
    nmzsubg.2
    nmzsubg.3
    @21
    @63
    grprinv
    syl2anc
    oveq1d
    @65
    @0
    @22
    @57
    @73
    @79
    @67
    wceq
    @74
    @81
    @75
    @77
    cX
    c.pl
    cG
    @3
    @9
    @60
    nmzsubg.2
    nmzsubg.3
    grpass
    syl13anc
    @65
    @0
    @73
    @80
    @60
    wceq
    @74
    @77
    cX
    c.pl
    cG
    @60
    @16
    nmzsubg.2
    nmzsubg.3
    @21
    grplid
    syl2anc
    3eqtr3d
    eleq1d
    @65
    @69
    @58
    cS
    @65
    @69
    @9
    @60
    @3
    c.pl
    co
    #
    c.pl
    co
    #
    @58
    @65
    @0
    @57
    @73
    @22
    @69
    @83
    wceq
    @74
    @75
    @77
    @81
    cX
    c.pl
    cG
    @9
    @60
    @3
    nmzsubg.2
    nmzsubg.3
    grpass
    syl13anc
    @65
    @82
    @29
    @9
    c.pl
    @65
    @82
    @29
    @9
    @3
    c.pl
    co
    #
    c.pl
    co
    #
    @29
    @16
    c.pl
    co
    #
    @29
    @65
    @0
    @37
    @57
    @22
    @82
    @85
    wceq
    @74
    @76
    @75
    @81
    cX
    c.pl
    cG
    @29
    @9
    @3
    nmzsubg.2
    nmzsubg.3
    grpass
    syl13anc
    @65
    @84
    @16
    @29
    c.pl
    @65
    @0
    @22
    @84
    @16
    wceq
    @74
    @81
    cX
    c.pl
    cG
    @8
    @3
    @16
    nmzsubg.2
    nmzsubg.3
    @21
    @63
    grplinv
    syl2anc
    oveq2d
    @65
    @0
    @37
    @86
    @29
    wceq
    @74
    @76
    cX
    c.pl
    cG
    @29
    @16
    nmzsubg.2
    nmzsubg.3
    @21
    grprid
    syl2anc
    3eqtrd
    oveq2d
    eqtrd
    eleq1d
    3bitr3rd
    ralrimiva
    vx
    vy
    vu
    @9
    c.pl
    cS
    cN
    cX
    elnmz.1
    elnmz
    sylanbrc
    jca
    ralrimiva
    vz
    vw
    cX
    c.pl
    cN
    cG
    @8
    nmzsubg.2
    nmzsubg.3
    @63
    issubg2
    mpbir3and
end
