include "ctgp.mm"
include "wcel.mm"
include "wa.mm"
include "cec.mm"
include "cv.mm"
include "crest.mm"
include "co.mm"
include "cconn.mm"
include "cpw.mm"
include "crab.mm"
include "cuni.mm"
include "wss.mm"
include "wbr.mm"
include "cab.mm"
include "wceq.mm"
include "dfec2.mm"
include "adantl.mm"
include "cminusg.mm"
include "cfv.mm"
include "cplusg.mm"
include "w3a.mm"
include "wb.mm"
include "ssrab2.mm"
include "sspwuni.mm"
include "mpbi.mm"
include "eqsstri.mm"
include "a1i.mm"
include "eqid.mm"
include "eqgval.mm"
include "syldan.mm"
include "simp2.mm"
include "syl6bi.mm"
include "abssdv.mm"
include "eqsstrd.mm"
include "simpr.mm"
include "cgrp.mm"
include "tgpgrp.mm"
include "grplinv.mm"
include "sylan.mm"
include "ctopon.mm"
include "tgptopon.mm"
include "adantr.mm"
include "grpidcl.mm"
include "syl.mm"
include "conncompid.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "mpbir3and.mm"
include "elecg.mm"
include "mpbird.mm"
include "cmpt.mm"
include "cima.mm"
include "eqglact.mm"
include "mp3an2.mm"
include "oveq2d.mm"
include "chmeo.mm"
include "ccn.mm"
include "tgplacthmeo.mm"
include "hmeocn.mm"
include "toponuni.mm"
include "syl5sseq.mm"
include "conncompconn.mm"
include "connima.mm"
include "conncompss.mm"
include "syl3anc.mm"
include "wral.mm"
include "wi.mm"
include "elpwi.mm"
include "ccnv.mm"
include "mptpreima.mm"
include "grprid.mm"
include "simprrl.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "elrab2.mm"
include "sylanbrc.mm"
include "hmeocnvcn.mm"
include "simprl.mm"
include "sseqtrd.mm"
include "simprrr.mm"
include "wfun.mm"
include "cdm.mm"
include "wf1o.mm"
include "grplactcnv.mm"
include "simpld.mm"
include "grplactfval.mm"
include "f1oeq1.mm"
include "mpbid.mm"
include "f1ocnv.mm"
include "f1ofun.mm"
include "3syl.mm"
include "f1odm.mm"
include "sseqtr4d.mm"
include "funimass3.mm"
include "imacnvcnv.mm"
include "syl6eqr.mm"
include "expr.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "ralrab.mm"
include "sylibr.mm"
include "unissb.mm"
include "eqssd.mm"

theorem tgpconncompeqg
  let vx: setvar x
  let cA: class A
  let c.sm: class .~
  let cS: class S
  let cG: class G
  let cJ: class J
  let cX: class X
  let c.0: class .0.
  let vy: setvar y
  let vz: setvar z
  let vg: setvar g
  let vw: setvar w
  assume tgpconncomp.x: |- X = ( Base ` G )
  assume tgpconncomp.z: |- .0. = ( 0g ` G )
  assume tgpconncomp.j: |- J = ( TopOpen ` G )
  assume tgpconncomp.s: |- S = U. { x e. ~P X | ( .0. e. x /\ ( J |`t x ) e. Conn ) }
  assume tgpconncompeqg.r: |- .~ = ( G ~QG S )

  disjoint .0. x
  disjoint A x
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
  assert |- ( ( G e. TopGrp /\ A e. X ) -> [ A ] .~ = U. { x e. ~P X | ( A e. x /\ ( J |`t x ) e. Conn ) } )

  proof
    cG
    ctgp
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cA
    c.sm
    cec
    #
    cA
    vx
    cv
    #
    wcel
    #
    cJ
    @4
    crest
    co
    #
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
    @2
    @3
    cX
    wss
    cA
    @3
    wcel
    #
    cJ
    @3
    crest
    co
    #
    cconn
    wcel
    @3
    @11
    wss
    @2
    @3
    cA
    vz
    cv
    #
    c.sm
    wbr
    #
    vz
    cab
    #
    cX
    @1
    @3
    @16
    wceq
    @0
    vz
    cA
    c.sm
    cX
    dfec2
    adantl
    @2
    @15
    vz
    cX
    @2
    @15
    @1
    @14
    cX
    wcel
    #
    cA
    cG
    cminusg
    cfv
    #
    cfv
    #
    @14
    cG
    cplusg
    cfv
    #
    co
    cS
    wcel
    #
    w3a
    #
    @17
    @0
    @1
    cS
    cX
    wss
    #
    @15
    @22
    wb
    @23
    @2
    cS
    c.0
    @4
    wcel
    @7
    wa
    #
    vx
    @9
    crab
    #
    cuni
    #
    cX
    tgpconncomp.s
    @25
    @9
    wss
    @26
    cX
    wss
    @24
    vx
    @9
    ssrab2
    @25
    cX
    sspwuni
    mpbi
    eqsstri
    #
    a1i
    #
    cA
    @14
    @20
    c.sm
    cS
    cG
    @18
    ctgp
    cX
    tgpconncomp.x
    @18
    eqid
    #
    @20
    eqid
    #
    tgpconncompeqg.r
    eqgval
    syldan
    @1
    @17
    @21
    simp2
    syl6bi
    abssdv
    eqsstrd
    @2
    @12
    cA
    cA
    c.sm
    wbr
    #
    @2
    @31
    @1
    @1
    @19
    cA
    @20
    co
    #
    cS
    wcel
    #
    @0
    @1
    simpr
    #
    @34
    @2
    @32
    c.0
    cS
    @0
    cG
    cgrp
    wcel
    #
    @1
    @32
    c.0
    wceq
    cG
    tgpgrp
    #
    cX
    @20
    cG
    @18
    cA
    c.0
    tgpconncomp.x
    @30
    tgpconncomp.z
    @29
    grplinv
    sylan
    @2
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
    c.0
    cS
    wcel
    @0
    @37
    @1
    cG
    cJ
    cX
    tgpconncomp.j
    tgpconncomp.x
    tgptopon
    adantr
    #
    @2
    @35
    @38
    @0
    @35
    @1
    @36
    adantr
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
    eqeltrd
    @0
    @1
    @23
    @31
    @1
    @1
    @33
    w3a
    wb
    @28
    cA
    cA
    @20
    c.sm
    cS
    cG
    @18
    ctgp
    cX
    tgpconncomp.x
    @29
    @30
    tgpconncompeqg.r
    eqgval
    syldan
    mpbir3and
    @2
    @1
    @1
    @12
    @31
    wb
    @34
    @34
    cA
    cA
    c.sm
    cX
    cX
    elecg
    syl2anc
    mpbird
    @2
    @13
    cJ
    vz
    cX
    cA
    @14
    @20
    co
    #
    cmpt
    #
    cS
    cima
    #
    crest
    co
    cconn
    @2
    @3
    @43
    cJ
    crest
    @0
    @35
    @1
    @3
    @43
    wceq
    #
    @36
    @35
    @23
    @1
    @44
    @27
    vz
    cA
    @20
    c.sm
    cG
    cX
    cS
    tgpconncomp.x
    tgpconncompeqg.r
    @30
    eqglact
    mp3an2
    sylan
    #
    oveq2d
    @2
    cS
    @42
    cJ
    cJ
    cJ
    cuni
    #
    @46
    eqid
    #
    @2
    @42
    cJ
    cJ
    chmeo
    co
    wcel
    #
    @42
    cJ
    cJ
    ccn
    co
    #
    wcel
    vz
    cA
    @20
    @42
    cG
    cJ
    cX
    @42
    eqid
    #
    tgpconncomp.x
    @30
    tgpconncomp.j
    tgplacthmeo
    #
    @42
    cJ
    cJ
    hmeocn
    syl
    @2
    cX
    cS
    @46
    @27
    @2
    @37
    cX
    @46
    wceq
    #
    @39
    cX
    cJ
    toponuni
    syl
    #
    syl5sseq
    @2
    @37
    @38
    cJ
    cS
    crest
    co
    cconn
    wcel
    @39
    @40
    vx
    c.0
    cS
    cJ
    cX
    tgpconncomp.s
    conncompconn
    syl2anc
    connima
    eqeltrd
    vx
    cA
    @11
    @3
    cJ
    cX
    @11
    eqid
    conncompss
    syl3anc
    @2
    vy
    cv
    #
    @3
    wss
    #
    vy
    @10
    wral
    #
    @11
    @3
    wss
    @2
    cA
    @54
    wcel
    #
    cJ
    @54
    crest
    co
    #
    cconn
    wcel
    #
    wa
    #
    @55
    wi
    #
    vy
    @9
    wral
    @56
    @2
    @61
    vy
    @9
    @54
    @9
    wcel
    @2
    @54
    cX
    wss
    #
    @61
    @54
    cX
    elpwi
    @2
    @62
    @60
    @55
    @2
    @62
    @60
    wa
    #
    wa
    #
    @54
    @42
    ccnv
    #
    ccnv
    cS
    cima
    #
    @3
    @64
    @65
    @54
    cima
    #
    cS
    wss
    #
    @54
    @66
    wss
    #
    @64
    @67
    cX
    wss
    #
    c.0
    @67
    wcel
    #
    cJ
    @67
    crest
    co
    cconn
    wcel
    @68
    @70
    @64
    @67
    @41
    @54
    wcel
    #
    vz
    cX
    crab
    cX
    vz
    cX
    @41
    @54
    @42
    @50
    mptpreima
    #
    @72
    vz
    cX
    ssrab2
    eqsstri
    a1i
    @64
    @38
    cA
    c.0
    @20
    co
    #
    @54
    wcel
    #
    @71
    @2
    @38
    @63
    @40
    adantr
    @64
    @74
    cA
    @54
    @2
    @74
    cA
    wceq
    #
    @63
    @0
    @35
    @1
    @76
    @36
    cX
    @20
    cG
    cA
    c.0
    tgpconncomp.x
    @30
    tgpconncomp.z
    grprid
    sylan
    adantr
    @2
    @62
    @57
    @59
    simprrl
    eqeltrd
    @72
    @75
    vz
    c.0
    cX
    @67
    @14
    c.0
    wceq
    @41
    @74
    @54
    @14
    c.0
    cA
    @20
    oveq2
    eleq1d
    @73
    elrab2
    sylanbrc
    @64
    @54
    @65
    cJ
    cJ
    @46
    @47
    @2
    @65
    @49
    wcel
    #
    @63
    @2
    @48
    @77
    @51
    @42
    cJ
    cJ
    hmeocnvcn
    syl
    adantr
    @64
    @54
    cX
    @46
    @2
    @62
    @60
    simprl
    #
    @2
    @52
    @63
    @53
    adantr
    sseqtrd
    @2
    @62
    @57
    @59
    simprrr
    connima
    vx
    c.0
    cS
    @67
    cJ
    cX
    tgpconncomp.s
    conncompss
    syl3anc
    @64
    @65
    wfun
    #
    @54
    @65
    cdm
    #
    wss
    @68
    @69
    wb
    @64
    cX
    cX
    @42
    wf1o
    #
    cX
    cX
    @65
    wf1o
    #
    @79
    @2
    @81
    @63
    @2
    cX
    cX
    cA
    vg
    cX
    vz
    cX
    vg
    cv
    @14
    @20
    co
    cmpt
    cmpt
    #
    cfv
    #
    wf1o
    #
    @81
    @2
    @85
    @84
    ccnv
    @19
    @83
    cfv
    wceq
    #
    @0
    @35
    @1
    @85
    @86
    wa
    @36
    cA
    @20
    vg
    @83
    cG
    @18
    cX
    vz
    @83
    eqid
    #
    tgpconncomp.x
    @30
    @29
    grplactcnv
    sylan
    simpld
    @2
    @84
    @42
    wceq
    #
    @85
    @81
    wb
    @1
    @88
    @0
    cA
    @20
    vg
    @83
    cG
    cX
    vz
    @87
    tgpconncomp.x
    grplactfval
    adantl
    cX
    cX
    @84
    @42
    f1oeq1
    syl
    mpbid
    adantr
    #
    cX
    cX
    @42
    f1ocnv
    #
    cX
    cX
    @65
    f1ofun
    3syl
    @64
    @54
    cX
    @80
    @78
    @64
    @81
    @82
    @80
    cX
    wceq
    @89
    @90
    cX
    cX
    @65
    f1odm
    3syl
    sseqtr4d
    @54
    cS
    @65
    funimass3
    syl2anc
    mpbid
    @64
    @3
    @43
    @66
    @2
    @44
    @63
    @45
    adantr
    @42
    cS
    imacnvcnv
    syl6eqr
    sseqtr4d
    expr
    sylan2
    ralrimiva
    @8
    @60
    @55
    vy
    vx
    @9
    @4
    @54
    wceq
    #
    @5
    @57
    @7
    @59
    @4
    @54
    cA
    eleq2
    @91
    @6
    @58
    cconn
    @4
    @54
    cJ
    crest
    oveq2
    eleq1d
    anbi12d
    ralrab
    sylibr
    vy
    @10
    @3
    unissb
    sylibr
    eqssd
end
