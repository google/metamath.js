include "ctgp.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wi.mm"
include "wral.mm"
include "cnsg.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "csg.mm"
include "crest.mm"
include "cconn.mm"
include "wa.mm"
include "cpw.mm"
include "crab.mm"
include "cuni.mm"
include "ssrab2.mm"
include "sspwuni.mm"
include "mpbi.mm"
include "eqsstri.mm"
include "a1i.mm"
include "ctopon.mm"
include "tgptopon.mm"
include "cgrp.mm"
include "tgpgrp.mm"
include "grpidcl.mm"
include "syl.mm"
include "conncompid.mm"
include "syl2anc.mm"
include "ne0i.mm"
include "cmpt.mm"
include "wf.mm"
include "crn.mm"
include "cima.mm"
include "cres.mm"
include "df-ima.mm"
include "wceq.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "rneqi.mm"
include "eqtri.mm"
include "imassrn.mm"
include "adantr.mm"
include "sselda.mm"
include "simpr.mm"
include "eqid.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "fmptd.mm"
include "frn.mm"
include "syl5ss.mm"
include "grpsubid.mm"
include "cvv.mm"
include "ovex.mm"
include "oveq2.mm"
include "elrnmpt1s.mm"
include "sylancl.mm"
include "eqeltrrd.mm"
include "syl6eleqr.mm"
include "chmeo.mm"
include "ccn.mm"
include "cminusg.mm"
include "ccom.mm"
include "grpsubval.mm"
include "sylan.mm"
include "mpteq2dva.mm"
include "grpinvcl.mm"
include "grpinvf.mm"
include "feqmptd.mm"
include "eqidd.mm"
include "fmptco.mm"
include "eqtr4d.mm"
include "grpinvhmeo.mm"
include "tgplacthmeo.mm"
include "syldan.mm"
include "hmeoco.mm"
include "eqeltrd.mm"
include "hmeocn.mm"
include "toponuni.mm"
include "syl5sseq.mm"
include "conncompconn.mm"
include "connima.mm"
include "conncompss.mm"
include "syl5eqssr.mm"
include "wfn.mm"
include "fnmpti.mm"
include "df-f.mm"
include "mpbiran.mm"
include "sylibr.mm"
include "fmpt.mm"
include "ralrimiva.mm"
include "w3a.mm"
include "wb.mm"
include "issubg4.mm"
include "mpbir3and.mm"
include "coppg.mm"
include "oppginv.mm"
include "fveq1d.mm"
include "simprll.mm"
include "grpinvinv.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "oppgplus.mm"
include "syl6eq.mm"
include "cqg.mm"
include "wbr.mm"
include "simprlr.mm"
include "simprr.mm"
include "eqgval.mm"
include "cec.mm"
include "tgpconncompeqg.mm"
include "oppgtgp.mm"
include "oppgbas.mm"
include "oppgid.mm"
include "oppgtopn.mm"
include "eleq2d.mm"
include "vex.mm"
include "fvex.mm"
include "elec.mm"
include "3bitr3g.mm"
include "mpbid.mm"
include "simp3d.mm"
include "expr.mm"
include "ralrimivva.mm"
include "isnsg2.mm"
include "sylanbrc.mm"

theorem tgpconncomp
  let vx: setvar x
  let cS: class S
  let cG: class G
  let cJ: class J
  let cX: class X
  let c.0: class .0.
  let vy: setvar y
  let vz: setvar z
  let c.sm: class .~
  let vg: setvar g
  let cA: class A
  let vw: setvar w
  assume tgpconncomp.x: |- X = ( Base ` G )
  assume tgpconncomp.z: |- .0. = ( 0g ` G )
  assume tgpconncomp.j: |- J = ( TopOpen ` G )
  assume tgpconncomp.s: |- S = U. { x e. ~P X | ( .0. e. x /\ ( J |`t x ) e. Conn ) }

  disjoint .0. x
  disjoint J x
  disjoint G x
  disjoint X x
  disjoint y z
  disjoint .~ y
  disjoint .~ z
  disjoint x z
  disjoint .0. z
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint J w
  disjoint J y
  disjoint J z
  disjoint S y
  disjoint S z
  disjoint g w
  disjoint G g
  disjoint G w
  disjoint G y
  disjoint G z
  disjoint X g
  disjoint X w
  disjoint X y
  disjoint X z
  assert |- ( G e. TopGrp -> S e. ( NrmSGrp ` G ) )

  proof
    cG
    ctgp
    wcel
    #
    cS
    cG
    csubg
    cfv
    wcel
    #
    vy
    cv
    #
    vz
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cS
    wcel
    #
    @3
    @2
    @4
    co
    #
    cS
    wcel
    #
    wi
    #
    vz
    cX
    wral
    vy
    cX
    wral
    cS
    cG
    cnsg
    cfv
    wcel
    @0
    @1
    cS
    cX
    wss
    #
    cS
    c0
    wne
    #
    @2
    @3
    cG
    csg
    cfv
    #
    co
    #
    cS
    wcel
    vz
    cS
    wral
    #
    vy
    cS
    wral
    #
    @10
    @0
    cS
    c.0
    vx
    cv
    #
    wcel
    cJ
    @16
    crest
    co
    cconn
    wcel
    #
    wa
    #
    vx
    cX
    cpw
    #
    crab
    #
    cuni
    #
    cX
    tgpconncomp.s
    @20
    @19
    wss
    @21
    cX
    wss
    @18
    vx
    @19
    ssrab2
    @20
    cX
    sspwuni
    mpbi
    eqsstri
    #
    a1i
    #
    @0
    c.0
    cS
    wcel
    #
    @11
    @0
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    c.0
    cX
    wcel
    #
    @24
    cG
    cJ
    cX
    tgpconncomp.j
    tgpconncomp.x
    tgptopon
    #
    @0
    cG
    cgrp
    wcel
    #
    @26
    cG
    tgpgrp
    #
    cX
    cG
    c.0
    tgpconncomp.x
    tgpconncomp.z
    grpidcl
    syl
    #
    vx
    c.0
    cS
    cJ
    cX
    tgpconncomp.s
    conncompid
    syl2anc
    cS
    c.0
    ne0i
    syl
    @0
    @14
    vy
    cS
    @0
    @2
    cS
    wcel
    #
    wa
    #
    cS
    cS
    vz
    cS
    @13
    cmpt
    #
    wf
    #
    @14
    @32
    @33
    crn
    #
    cS
    wss
    #
    @34
    @32
    @35
    vz
    cX
    @13
    cmpt
    #
    cS
    cima
    #
    cS
    @38
    @37
    cS
    cres
    #
    crn
    @35
    @37
    cS
    df-ima
    @39
    @33
    @10
    @39
    @33
    wceq
    @22
    vz
    cX
    cS
    @13
    resmpt
    ax-mp
    rneqi
    eqtri
    #
    @32
    @38
    cX
    wss
    c.0
    @38
    wcel
    cJ
    @38
    crest
    co
    cconn
    wcel
    @38
    cS
    wss
    @32
    @38
    @37
    crn
    #
    cX
    @37
    cS
    imassrn
    @32
    cX
    cX
    @37
    wf
    @41
    cX
    wss
    @32
    vz
    cX
    @13
    cX
    @37
    @32
    @3
    cX
    wcel
    #
    wa
    @28
    @2
    cX
    wcel
    #
    @42
    @13
    cX
    wcel
    @32
    @28
    @42
    @0
    @28
    @31
    @29
    adantr
    #
    adantr
    @32
    @43
    @42
    @0
    cS
    cX
    @2
    @23
    sselda
    #
    adantr
    @32
    @42
    simpr
    cX
    cG
    @12
    @2
    @3
    tgpconncomp.x
    @12
    eqid
    #
    grpsubcl
    syl3anc
    @37
    eqid
    fmptd
    cX
    cX
    @37
    frn
    syl
    syl5ss
    @32
    c.0
    @35
    @38
    @32
    @2
    @2
    @12
    co
    #
    c.0
    @35
    @32
    @28
    @43
    @47
    c.0
    wceq
    @44
    @45
    cX
    cG
    @12
    @2
    c.0
    tgpconncomp.x
    tgpconncomp.z
    @46
    grpsubid
    syl2anc
    @32
    @31
    @47
    cvv
    wcel
    @47
    @35
    wcel
    @0
    @31
    simpr
    @2
    @2
    @12
    ovex
    vz
    cS
    @13
    @47
    @2
    @33
    cvv
    @33
    eqid
    #
    @3
    @2
    @2
    @12
    oveq2
    elrnmpt1s
    sylancl
    eqeltrrd
    @40
    syl6eleqr
    @32
    cS
    @37
    cJ
    cJ
    cJ
    cuni
    #
    @49
    eqid
    @32
    @37
    cJ
    cJ
    chmeo
    co
    #
    wcel
    @37
    cJ
    cJ
    ccn
    co
    wcel
    @32
    @37
    vw
    cX
    @2
    vw
    cv
    #
    @4
    co
    #
    cmpt
    #
    cG
    cminusg
    cfv
    #
    ccom
    #
    @50
    @32
    @37
    vz
    cX
    @2
    @3
    @54
    cfv
    #
    @4
    co
    #
    cmpt
    @55
    @32
    vz
    cX
    @13
    @57
    @32
    @43
    @42
    @13
    @57
    wceq
    @45
    cX
    @4
    cG
    @54
    @12
    @2
    @3
    tgpconncomp.x
    @4
    eqid
    #
    @54
    eqid
    #
    @46
    grpsubval
    sylan
    mpteq2dva
    @32
    vz
    vw
    cX
    cX
    @56
    @52
    @57
    @54
    @53
    @32
    @28
    @42
    @56
    cX
    wcel
    @44
    cX
    cG
    @54
    @3
    tgpconncomp.x
    @59
    grpinvcl
    sylan
    @32
    vz
    cX
    cX
    @54
    @0
    cX
    cX
    @54
    wf
    #
    @31
    @0
    @28
    @60
    @29
    cX
    cG
    @54
    tgpconncomp.x
    @59
    grpinvf
    syl
    adantr
    feqmptd
    @32
    @53
    eqidd
    @51
    @56
    @2
    @4
    oveq2
    fmptco
    eqtr4d
    @32
    @54
    @50
    wcel
    #
    @53
    @50
    wcel
    #
    @55
    @50
    wcel
    @0
    @61
    @31
    cG
    @54
    cJ
    tgpconncomp.j
    @59
    grpinvhmeo
    adantr
    @0
    @31
    @43
    @62
    @45
    vw
    @2
    @4
    @53
    cG
    cJ
    cX
    @53
    eqid
    tgpconncomp.x
    @58
    tgpconncomp.j
    tgplacthmeo
    syldan
    @54
    @53
    cJ
    cJ
    cJ
    hmeoco
    syl2anc
    eqeltrd
    @37
    cJ
    cJ
    hmeocn
    syl
    @32
    cX
    cS
    @49
    @22
    @0
    cX
    @49
    wceq
    #
    @31
    @0
    @25
    @63
    @27
    cX
    cJ
    toponuni
    syl
    adantr
    syl5sseq
    @0
    cJ
    cS
    crest
    co
    cconn
    wcel
    #
    @31
    @0
    @25
    @26
    @64
    @27
    @30
    vx
    c.0
    cS
    cJ
    cX
    tgpconncomp.s
    conncompconn
    syl2anc
    adantr
    connima
    vx
    c.0
    cS
    @38
    cJ
    cX
    tgpconncomp.s
    conncompss
    syl3anc
    syl5eqssr
    @34
    @33
    cS
    wfn
    @36
    vz
    cS
    @13
    @33
    @2
    @3
    @12
    ovex
    @48
    fnmpti
    cS
    cS
    @33
    df-f
    mpbiran
    sylibr
    vz
    cS
    cS
    @13
    @33
    @48
    fmpt
    sylibr
    ralrimiva
    @0
    @28
    @1
    @10
    @11
    @15
    w3a
    wb
    @29
    vy
    vz
    cX
    cS
    cG
    @12
    tgpconncomp.x
    @46
    issubg4
    syl
    mpbir3and
    @0
    @9
    vy
    vz
    cX
    cX
    @0
    @43
    @42
    wa
    #
    @6
    @8
    @0
    @65
    @6
    wa
    #
    wa
    #
    @2
    @54
    cfv
    #
    cG
    coppg
    cfv
    #
    cminusg
    cfv
    #
    cfv
    #
    @3
    @69
    cplusg
    cfv
    #
    co
    #
    @7
    cS
    @67
    @73
    @2
    @3
    @72
    co
    @7
    @67
    @71
    @2
    @3
    @72
    @67
    @68
    @54
    cfv
    #
    @71
    @2
    @67
    @68
    @54
    @70
    @67
    @28
    @54
    @70
    wceq
    @0
    @28
    @66
    @29
    adantr
    #
    cG
    @54
    @69
    @69
    eqid
    #
    @59
    oppginv
    syl
    fveq1d
    @67
    @28
    @43
    @74
    @2
    wceq
    @75
    @0
    @43
    @42
    @6
    simprll
    #
    cX
    cG
    @54
    @2
    tgpconncomp.x
    @59
    grpinvinv
    syl2anc
    #
    eqtr3d
    oveq1d
    @4
    @72
    cG
    @69
    @2
    @3
    @58
    @76
    @72
    eqid
    #
    oppgplus
    syl6eq
    @67
    @68
    cX
    wcel
    #
    @42
    @73
    cS
    wcel
    #
    @67
    @68
    @3
    @69
    cS
    cqg
    co
    #
    wbr
    #
    @80
    @42
    @81
    w3a
    #
    @67
    @68
    @3
    cG
    cS
    cqg
    co
    #
    wbr
    #
    @83
    @67
    @86
    @80
    @42
    @74
    @3
    @4
    co
    #
    cS
    wcel
    #
    @67
    @28
    @43
    @80
    @75
    @77
    cX
    cG
    @54
    @2
    tgpconncomp.x
    @59
    grpinvcl
    syl2anc
    #
    @0
    @43
    @42
    @6
    simprlr
    @67
    @87
    @5
    cS
    @67
    @74
    @2
    @3
    @4
    @78
    oveq1d
    @0
    @65
    @6
    simprr
    eqeltrd
    @67
    @28
    @10
    @86
    @80
    @42
    @88
    w3a
    wb
    @75
    @22
    @68
    @3
    @4
    @85
    cS
    cG
    @54
    cgrp
    cX
    tgpconncomp.x
    @59
    @58
    @85
    eqid
    #
    eqgval
    sylancl
    mpbir3and
    @67
    @3
    @68
    @85
    cec
    #
    wcel
    @3
    @68
    @82
    cec
    #
    wcel
    @86
    @83
    @67
    @91
    @92
    @3
    @67
    @91
    @68
    @16
    wcel
    @17
    wa
    vx
    @19
    crab
    cuni
    #
    @92
    @0
    @66
    @80
    @91
    @93
    wceq
    @89
    vx
    @68
    @85
    cS
    cG
    cJ
    cX
    c.0
    tgpconncomp.x
    tgpconncomp.z
    tgpconncomp.j
    tgpconncomp.s
    @90
    tgpconncompeqg
    syldan
    @67
    @69
    ctgp
    wcel
    #
    @80
    @92
    @93
    wceq
    @0
    @94
    @66
    cG
    @69
    @76
    oppgtgp
    adantr
    #
    @89
    vx
    @68
    @82
    cS
    @69
    cJ
    cX
    c.0
    cX
    cG
    @69
    @76
    tgpconncomp.x
    oppgbas
    #
    cG
    @69
    c.0
    @76
    tgpconncomp.z
    oppgid
    cG
    cJ
    @69
    @76
    tgpconncomp.j
    oppgtopn
    tgpconncomp.s
    @82
    eqid
    #
    tgpconncompeqg
    syl2anc
    eqtr4d
    eleq2d
    @3
    @68
    @85
    vz
    vex
    #
    @2
    @54
    fvex
    #
    elec
    @3
    @68
    @82
    @98
    @99
    elec
    3bitr3g
    mpbid
    @67
    @94
    @10
    @83
    @84
    wb
    @95
    @22
    @68
    @3
    @72
    @82
    cS
    @69
    @70
    ctgp
    cX
    @96
    @70
    eqid
    @79
    @97
    eqgval
    sylancl
    mpbid
    simp3d
    eqeltrrd
    expr
    ralrimivva
    vy
    vz
    @4
    cS
    cG
    cX
    tgpconncomp.x
    @58
    isnsg2
    sylanbrc
end
