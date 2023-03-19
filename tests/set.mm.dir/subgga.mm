include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cgrp.mm"
include "cvv.mm"
include "wa.mm"
include "cbs.mm"
include "cxp.mm"
include "wf.mm"
include "c0g.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "cplusg.mm"
include "wral.mm"
include "cga.mm"
include "subggrp.mm"
include "fvex.mm"
include "eqeltri.mm"
include "jctir.mm"
include "subgrcl.mm"
include "adantr.mm"
include "subgss.mm"
include "sselda.mm"
include "adantrr.mm"
include "simprr.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "ralrimivva.mm"
include "fmpt2.mm"
include "sylib.mm"
include "subgbas.mm"
include "xpeq1d.mm"
include "feq2d.mm"
include "mpbid.mm"
include "eqid.mm"
include "subg0cl.mm"
include "oveq12.mm"
include "ovex.mm"
include "ovmpt2a.mm"
include "sylan.mm"
include "subg0.mm"
include "oveq1d.mm"
include "grplid.mm"
include "3eqtr3d.mm"
include "ad2antrr.mm"
include "wss.mm"
include "simprl.mm"
include "sseldd.mm"
include "simplr.mm"
include "grpass.mm"
include "syl13anc.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "subgcl.mm"
include "3expb.mm"
include "adantlr.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "ressplusg.mm"
include "oveqd.mm"
include "eqeq1d.mm"
include "raleqbidv.mm"
include "biimpa.mm"
include "syldan.mm"
include "jca.mm"
include "ralrimiva.mm"
include "isga.mm"
include "sylanbrc.mm"

theorem subgga
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume subgga.1: |- X = ( Base ` G )
  assume subgga.2: |- .+ = ( +g ` G )
  assume subgga.3: |- H = ( G |`s Y )
  assume subgga.4: |- F = ( x e. Y , y e. X |-> ( x .+ y ) )

  disjoint x y
  disjoint G x
  disjoint G y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint .+ x
  disjoint .+ y
  disjoint u v
  disjoint u w
  disjoint F u
  disjoint v w
  disjoint F v
  disjoint F w
  disjoint u x
  disjoint u y
  disjoint G u
  disjoint v x
  disjoint v y
  disjoint G v
  disjoint w x
  disjoint w y
  disjoint G w
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint H u
  disjoint H v
  disjoint H w
  assert |- ( Y e. ( SubGrp ` G ) -> F e. ( H GrpAct X ) )

  proof
    cY
    cG
    csubg
    cfv
    #
    wcel
    #
    cH
    cgrp
    wcel
    #
    cX
    cvv
    wcel
    #
    wa
    cH
    cbs
    cfv
    #
    cX
    cxp
    #
    cX
    cF
    wf
    #
    cH
    c0g
    cfv
    #
    vu
    cv
    #
    cF
    co
    #
    @8
    wceq
    #
    vv
    cv
    #
    vw
    cv
    #
    cH
    cplusg
    cfv
    #
    co
    #
    @8
    cF
    co
    #
    @11
    @12
    @8
    cF
    co
    #
    cF
    co
    #
    wceq
    #
    vw
    @4
    wral
    #
    vv
    @4
    wral
    #
    wa
    #
    vu
    cX
    wral
    #
    wa
    cF
    cH
    cX
    cga
    co
    wcel
    @1
    @2
    @3
    cY
    cG
    cH
    subgga.3
    subggrp
    cX
    cG
    cbs
    cfv
    cvv
    subgga.1
    cG
    cbs
    fvex
    eqeltri
    jctir
    @1
    @6
    @22
    @1
    cY
    cX
    cxp
    #
    cX
    cF
    wf
    #
    @6
    @1
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    #
    cX
    wcel
    #
    vy
    cX
    wral
    vx
    cY
    wral
    @24
    @1
    @28
    vx
    vy
    cY
    cX
    @1
    @25
    cY
    wcel
    #
    @26
    cX
    wcel
    #
    wa
    #
    wa
    cG
    cgrp
    wcel
    #
    @25
    cX
    wcel
    #
    @30
    @28
    @1
    @32
    @31
    cY
    cG
    subgrcl
    #
    adantr
    @1
    @29
    @33
    @30
    @1
    cY
    cX
    @25
    cX
    cY
    cG
    subgga.1
    subgss
    #
    sselda
    adantrr
    @1
    @29
    @30
    simprr
    cX
    c.pl
    cG
    @25
    @26
    subgga.1
    subgga.2
    grpcl
    syl3anc
    ralrimivva
    vx
    vy
    cY
    cX
    @27
    cX
    cF
    subgga.4
    fmpt2
    sylib
    @1
    @23
    @5
    cX
    cF
    @1
    cY
    @4
    cX
    cY
    cG
    cH
    subgga.3
    subgbas
    #
    xpeq1d
    feq2d
    mpbid
    @1
    @21
    vu
    cX
    @1
    @8
    cX
    wcel
    #
    wa
    #
    @10
    @20
    @38
    cG
    c0g
    cfv
    #
    @8
    cF
    co
    #
    @39
    @8
    c.pl
    co
    #
    @9
    @8
    @1
    @39
    cY
    wcel
    @37
    @40
    @41
    wceq
    cY
    cG
    @39
    @39
    eqid
    #
    subg0cl
    vx
    vy
    @39
    @8
    cY
    cX
    @27
    @41
    cF
    @25
    @39
    @26
    @8
    c.pl
    oveq12
    subgga.4
    @39
    @8
    c.pl
    ovex
    ovmpt2a
    sylan
    @1
    @40
    @9
    wceq
    @37
    @1
    @39
    @7
    @8
    cF
    cY
    cG
    cH
    @39
    subgga.3
    @42
    subg0
    oveq1d
    adantr
    @1
    @32
    @37
    @41
    @8
    wceq
    @34
    cX
    c.pl
    cG
    @8
    @39
    subgga.1
    subgga.2
    @42
    grplid
    sylan
    3eqtr3d
    @1
    @37
    @11
    @12
    c.pl
    co
    #
    @8
    cF
    co
    #
    @17
    wceq
    #
    vw
    cY
    wral
    #
    vv
    cY
    wral
    #
    @20
    @38
    @45
    vv
    vw
    cY
    cY
    @38
    @11
    cY
    wcel
    #
    @12
    cY
    wcel
    #
    wa
    #
    wa
    #
    @43
    @8
    c.pl
    co
    #
    @11
    @12
    @8
    c.pl
    co
    #
    cF
    co
    #
    @44
    @17
    @51
    @52
    @11
    @53
    c.pl
    co
    #
    @54
    @51
    @32
    @11
    cX
    wcel
    @12
    cX
    wcel
    #
    @37
    @52
    @55
    wceq
    @1
    @32
    @37
    @50
    @34
    ad2antrr
    #
    @51
    cY
    cX
    @11
    @1
    cY
    cX
    wss
    @37
    @50
    @35
    ad2antrr
    #
    @38
    @48
    @49
    simprl
    #
    sseldd
    @51
    cY
    cX
    @12
    @58
    @38
    @48
    @49
    simprr
    #
    sseldd
    #
    @1
    @37
    @50
    simplr
    #
    cX
    c.pl
    cG
    @11
    @12
    @8
    subgga.1
    subgga.2
    grpass
    syl13anc
    @51
    @48
    @53
    cX
    wcel
    #
    @54
    @55
    wceq
    @59
    @51
    @32
    @56
    @37
    @63
    @57
    @61
    @62
    cX
    c.pl
    cG
    @12
    @8
    subgga.1
    subgga.2
    grpcl
    syl3anc
    vx
    vy
    @11
    @53
    cY
    cX
    @27
    @55
    cF
    @25
    @11
    @26
    @53
    c.pl
    oveq12
    subgga.4
    @11
    @53
    c.pl
    ovex
    ovmpt2a
    syl2anc
    eqtr4d
    @51
    @43
    cY
    wcel
    #
    @37
    @44
    @52
    wceq
    @1
    @50
    @64
    @37
    @1
    @48
    @49
    @64
    c.pl
    cY
    cG
    @11
    @12
    subgga.2
    subgcl
    3expb
    adantlr
    @62
    vx
    vy
    @43
    @8
    cY
    cX
    @27
    @52
    cF
    @25
    @43
    @26
    @8
    c.pl
    oveq12
    subgga.4
    @43
    @8
    c.pl
    ovex
    ovmpt2a
    syl2anc
    @51
    @16
    @53
    @11
    cF
    @51
    @49
    @37
    @16
    @53
    wceq
    @60
    @62
    vx
    vy
    @12
    @8
    cY
    cX
    @27
    @53
    cF
    @25
    @12
    @26
    @8
    c.pl
    oveq12
    subgga.4
    @12
    @8
    c.pl
    ovex
    ovmpt2a
    syl2anc
    oveq2d
    3eqtr4d
    ralrimivva
    @1
    @47
    @20
    @1
    @46
    @19
    vv
    cY
    @4
    @36
    @1
    @45
    @18
    vw
    cY
    @4
    @36
    @1
    @44
    @15
    @17
    @1
    @43
    @14
    @8
    cF
    @1
    c.pl
    @13
    @11
    @12
    cY
    c.pl
    cG
    cH
    @0
    subgga.3
    subgga.2
    ressplusg
    oveqd
    oveq1d
    eqeq1d
    raleqbidv
    raleqbidv
    biimpa
    syldan
    jca
    ralrimiva
    jca
    vu
    vv
    vw
    @13
    cF
    cH
    @4
    cX
    @7
    @4
    eqid
    @13
    eqid
    @7
    eqid
    isga
    sylanbrc
end
