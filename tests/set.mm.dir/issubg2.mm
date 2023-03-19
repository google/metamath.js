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
include "wa.mm"
include "w3a.mm"
include "subgss.mm"
include "cress.mm"
include "cbs.mm"
include "eqid.mm"
include "subgbas.mm"
include "subggrp.mm"
include "grpbn0.mm"
include "syl.mm"
include "eqnetrd.mm"
include "subgcl.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "subginvcl.mm"
include "jca.mm"
include "3jca.mm"
include "simpl.mm"
include "simpr1.mm"
include "c0g.mm"
include "wceq.mm"
include "ressbas2.mm"
include "cvv.mm"
include "cplusg.mm"
include "fvex.mm"
include "syl6eqel.mm"
include "ressplusg.mm"
include "simpr3.mm"
include "ralimi.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "syl5com.mm"
include "3impib.mm"
include "sseld.mm"
include "3anim123d.mm"
include "imp.mm"
include "grpass.mm"
include "adantlr.mm"
include "syldan.mm"
include "wex.mm"
include "simpr2.mm"
include "n0.mm"
include "sylib.mm"
include "sselda.mm"
include "grplinv.mm"
include "simpr.mm"
include "fveq2.mm"
include "rspccva.mm"
include "sylan.mm"
include "adantr.mm"
include "ovrspc2v.mm"
include "syl21anc.mm"
include "eqeltrrd.mm"
include "exlimddv.mm"
include "grplid.mm"
include "isgrpd.mm"
include "issubg.mm"
include "syl3anbrc.mm"
include "ex.mm"
include "impbid2.mm"

theorem issubg2
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let cG: class G
  let cI: class I
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume issubg2.b: |- B = ( Base ` G )
  assume issubg2.p: |- .+ = ( +g ` G )
  assume issubg2.i: |- I = ( invg ` G )

  disjoint x y
  disjoint G x
  disjoint G y
  disjoint I x
  disjoint I y
  disjoint .+ x
  disjoint .+ y
  disjoint S x
  disjoint S y
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint G u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint G v
  disjoint w x
  disjoint w y
  disjoint G w
  disjoint I u
  disjoint I v
  disjoint I w
  disjoint .+ u
  disjoint .+ v
  disjoint .+ w
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint B u
  disjoint B v
  disjoint B w
  assert |- ( G e. Grp -> ( S e. ( SubGrp ` G ) <-> ( S C_ B /\ S =/= (/) /\ A. x e. S ( A. y e. S ( x .+ y ) e. S /\ ( I ` x ) e. S ) ) ) )

  proof
    cG
    cgrp
    wcel
    #
    cS
    cG
    csubg
    cfv
    wcel
    #
    cS
    cB
    wss
    #
    cS
    c0
    wne
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
    cS
    wcel
    #
    vy
    cS
    wral
    #
    @4
    cI
    cfv
    #
    cS
    wcel
    #
    wa
    #
    vx
    cS
    wral
    #
    w3a
    #
    @1
    @2
    @3
    @12
    cB
    cS
    cG
    issubg2.b
    subgss
    @1
    cS
    cG
    cS
    cress
    co
    #
    cbs
    cfv
    #
    c0
    cS
    cG
    @14
    @14
    eqid
    #
    subgbas
    @1
    @14
    cgrp
    wcel
    #
    @15
    c0
    wne
    cS
    cG
    @14
    @16
    subggrp
    @15
    @14
    @15
    eqid
    grpbn0
    syl
    eqnetrd
    @1
    @11
    vx
    cS
    @1
    @4
    cS
    wcel
    #
    wa
    #
    @8
    @10
    @19
    @7
    vy
    cS
    @1
    @18
    @5
    cS
    wcel
    @7
    c.pl
    cS
    cG
    @4
    @5
    issubg2.p
    subgcl
    3expa
    ralrimiva
    cS
    cG
    cI
    @4
    issubg2.i
    subginvcl
    jca
    ralrimiva
    3jca
    @0
    @13
    @1
    @0
    @13
    wa
    #
    @0
    @2
    @17
    @1
    @0
    @13
    simpl
    @0
    @2
    @3
    @12
    simpr1
    #
    @20
    vu
    vv
    vw
    cS
    c.pl
    @14
    vu
    cv
    #
    cI
    cfv
    #
    cG
    c0g
    cfv
    #
    @20
    @2
    cS
    @15
    wceq
    @21
    cS
    cB
    @14
    cG
    @16
    issubg2.b
    ressbas2
    syl
    #
    @20
    cS
    cvv
    wcel
    c.pl
    @14
    cplusg
    cfv
    wceq
    @20
    cS
    @15
    cvv
    @25
    @14
    cbs
    fvex
    syl6eqel
    cS
    c.pl
    cG
    @14
    cvv
    @16
    issubg2.p
    ressplusg
    syl
    @20
    @22
    cS
    wcel
    #
    vv
    cv
    #
    cS
    wcel
    #
    @22
    @27
    c.pl
    co
    #
    cS
    wcel
    #
    @20
    @8
    vx
    cS
    wral
    #
    @26
    @28
    wa
    @30
    @20
    @12
    @31
    @0
    @2
    @3
    @12
    simpr3
    #
    @11
    @8
    vx
    cS
    @8
    @10
    simpl
    ralimi
    syl
    #
    @7
    @30
    @22
    @5
    c.pl
    co
    #
    cS
    wcel
    vx
    vy
    @22
    @27
    cS
    cS
    @4
    @22
    wceq
    #
    @6
    @34
    cS
    @4
    @22
    @5
    c.pl
    oveq1
    eleq1d
    @5
    @27
    wceq
    @34
    @29
    cS
    @5
    @27
    @22
    c.pl
    oveq2
    eleq1d
    rspc2v
    syl5com
    3impib
    @20
    @26
    @28
    vw
    cv
    #
    cS
    wcel
    #
    w3a
    #
    @22
    cB
    wcel
    #
    @27
    cB
    wcel
    #
    @36
    cB
    wcel
    #
    w3a
    #
    @29
    @36
    c.pl
    co
    @22
    @27
    @36
    c.pl
    co
    c.pl
    co
    wceq
    #
    @20
    @38
    @42
    @20
    @26
    @39
    @28
    @40
    @37
    @41
    @20
    cS
    cB
    @22
    @21
    sseld
    @20
    cS
    cB
    @27
    @21
    sseld
    @20
    cS
    cB
    @36
    @21
    sseld
    3anim123d
    imp
    @0
    @42
    @43
    @13
    cB
    c.pl
    cG
    @22
    @27
    @36
    issubg2.b
    issubg2.p
    grpass
    adantlr
    syldan
    @20
    @26
    @24
    cS
    wcel
    vu
    @20
    @3
    @26
    vu
    wex
    @0
    @2
    @3
    @12
    simpr2
    vu
    cS
    n0
    sylib
    @20
    @26
    wa
    #
    @23
    @22
    c.pl
    co
    #
    @24
    cS
    @20
    @26
    @39
    @45
    @24
    wceq
    #
    @20
    cS
    cB
    @22
    @21
    sselda
    #
    @0
    @39
    @46
    @13
    cB
    c.pl
    cG
    cI
    @22
    @24
    issubg2.b
    issubg2.p
    @24
    eqid
    #
    issubg2.i
    grplinv
    adantlr
    syldan
    #
    @44
    @23
    cS
    wcel
    #
    @26
    @31
    @45
    cS
    wcel
    @20
    @10
    vx
    cS
    wral
    #
    @26
    @50
    @20
    @12
    @51
    @32
    @11
    @10
    vx
    cS
    @8
    @10
    simpr
    ralimi
    syl
    @10
    @50
    vx
    @22
    cS
    @35
    @9
    @23
    cS
    @4
    @22
    cI
    fveq2
    eleq1d
    rspccva
    sylan
    #
    @20
    @26
    simpr
    @20
    @31
    @26
    @33
    adantr
    vx
    vy
    cS
    cS
    cS
    c.pl
    @23
    @22
    ovrspc2v
    syl21anc
    eqeltrrd
    exlimddv
    @20
    @26
    @39
    @24
    @22
    c.pl
    co
    @22
    wceq
    #
    @47
    @0
    @39
    @53
    @13
    cB
    c.pl
    cG
    @22
    @24
    issubg2.b
    issubg2.p
    @48
    grplid
    adantlr
    syldan
    @52
    @49
    isgrpd
    cB
    cS
    cG
    issubg2.b
    issubg
    syl3anbrc
    ex
    impbid2
end
