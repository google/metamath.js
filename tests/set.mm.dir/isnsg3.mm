include "cnsg.mm"
include "cfv.mm"
include "wcel.mm"
include "csubg.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "nsgsubg.mm"
include "nsgconj.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "jca.mm"
include "wi.mm"
include "simpl.mm"
include "cminusg.mm"
include "c0g.mm"
include "cgrp.mm"
include "wceq.mm"
include "subgrcl.mm"
include "ad2antrr.mm"
include "simprll.mm"
include "eqid.mm"
include "grplinv.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "grpinvcl.mm"
include "simprlr.mm"
include "grpass.mm"
include "syl13anc.mm"
include "grplid.mm"
include "3eqtr3d.mm"
include "grpsubinv.mm"
include "eqtrd.mm"
include "simprr.mm"
include "simplr.mm"
include "oveq1.mm"
include "id.mm"
include "oveq12d.mm"
include "eleq1d.mm"
include "oveq2.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "eqeltrrd.mm"
include "expr.mm"
include "isnsg2.mm"
include "sylanbrc.mm"
include "impbii.mm"

theorem isnsg3
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let cS: class S
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let vw: setvar w
  let vz: setvar z
  assume isnsg3.1: |- X = ( Base ` G )
  assume isnsg3.2: |- .+ = ( +g ` G )
  assume isnsg3.3: |- .- = ( -g ` G )

  disjoint x y
  disjoint .- x
  disjoint .- y
  disjoint G x
  disjoint G y
  disjoint .+ x
  disjoint .+ y
  disjoint S x
  disjoint S y
  disjoint X x
  disjoint X y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint .- w
  disjoint x z
  disjoint y z
  disjoint .- z
  disjoint G w
  disjoint G z
  disjoint .+ w
  disjoint .+ z
  disjoint S w
  disjoint S z
  disjoint X w
  disjoint X z
  assert |- ( S e. ( NrmSGrp ` G ) <-> ( S e. ( SubGrp ` G ) /\ A. x e. X A. y e. S ( ( x .+ y ) .- x ) e. S ) )

  proof
    cS
    cG
    cnsg
    cfv
    wcel
    #
    cS
    cG
    csubg
    cfv
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    #
    @2
    c.mi
    co
    #
    cS
    wcel
    #
    vy
    cS
    wral
    vx
    cX
    wral
    #
    wa
    #
    @0
    @1
    @7
    cS
    cG
    nsgsubg
    @0
    @6
    vx
    vy
    cX
    cS
    @0
    @2
    cX
    wcel
    @3
    cS
    wcel
    @6
    @2
    @3
    c.pl
    cS
    cG
    c.mi
    cX
    isnsg3.1
    isnsg3.2
    isnsg3.3
    nsgconj
    3expb
    ralrimivva
    jca
    @8
    @1
    vz
    cv
    #
    vw
    cv
    #
    c.pl
    co
    #
    cS
    wcel
    #
    @10
    @9
    c.pl
    co
    #
    cS
    wcel
    #
    wi
    #
    vw
    cX
    wral
    vz
    cX
    wral
    @0
    @1
    @7
    simpl
    @8
    @15
    vz
    vw
    cX
    cX
    @8
    @9
    cX
    wcel
    #
    @10
    cX
    wcel
    #
    wa
    #
    @12
    @14
    @8
    @18
    @12
    wa
    #
    wa
    #
    @9
    cG
    cminusg
    cfv
    #
    cfv
    #
    @11
    c.pl
    co
    #
    @22
    c.mi
    co
    #
    @13
    cS
    @20
    @24
    @10
    @22
    c.mi
    co
    @13
    @20
    @23
    @10
    @22
    c.mi
    @20
    @22
    @9
    c.pl
    co
    #
    @10
    c.pl
    co
    #
    cG
    c0g
    cfv
    #
    @10
    c.pl
    co
    #
    @23
    @10
    @20
    @25
    @27
    @10
    c.pl
    @20
    cG
    cgrp
    wcel
    #
    @16
    @25
    @27
    wceq
    @1
    @29
    @7
    @19
    cS
    cG
    subgrcl
    ad2antrr
    #
    @8
    @16
    @17
    @12
    simprll
    #
    cX
    c.pl
    cG
    @21
    @9
    @27
    isnsg3.1
    isnsg3.2
    @27
    eqid
    #
    @21
    eqid
    #
    grplinv
    syl2anc
    oveq1d
    @20
    @29
    @22
    cX
    wcel
    #
    @16
    @17
    @26
    @23
    wceq
    @30
    @20
    @29
    @16
    @34
    @30
    @31
    cX
    cG
    @21
    @9
    isnsg3.1
    @33
    grpinvcl
    syl2anc
    #
    @31
    @8
    @16
    @17
    @12
    simprlr
    #
    cX
    c.pl
    cG
    @22
    @9
    @10
    isnsg3.1
    isnsg3.2
    grpass
    syl13anc
    @20
    @29
    @17
    @28
    @10
    wceq
    @30
    @36
    cX
    c.pl
    cG
    @10
    @27
    isnsg3.1
    isnsg3.2
    @32
    grplid
    syl2anc
    3eqtr3d
    oveq1d
    @20
    cX
    c.pl
    cG
    c.mi
    @21
    @10
    @9
    isnsg3.1
    isnsg3.2
    isnsg3.3
    @33
    @30
    @36
    @31
    grpsubinv
    eqtrd
    @20
    @34
    @12
    @7
    @24
    cS
    wcel
    #
    @35
    @8
    @18
    @12
    simprr
    @1
    @7
    @19
    simplr
    @6
    @37
    @22
    @3
    c.pl
    co
    #
    @22
    c.mi
    co
    #
    cS
    wcel
    vx
    vy
    @22
    @11
    cX
    cS
    @2
    @22
    wceq
    #
    @5
    @39
    cS
    @40
    @4
    @38
    @2
    @22
    c.mi
    @2
    @22
    @3
    c.pl
    oveq1
    @40
    id
    oveq12d
    eleq1d
    @3
    @11
    wceq
    #
    @39
    @24
    cS
    @41
    @38
    @23
    @22
    c.mi
    @3
    @11
    @22
    c.pl
    oveq2
    oveq1d
    eleq1d
    rspc2va
    syl21anc
    eqeltrrd
    expr
    ralrimivva
    vz
    vw
    c.pl
    cS
    cG
    cX
    isnsg3.1
    isnsg3.2
    isnsg2
    sylanbrc
    impbii
end
