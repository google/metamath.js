include "crg.mm"
include "wcel.mm"
include "csubrg.mm"
include "cfv.mm"
include "csubg.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "w3a.mm"
include "subrgsubg.mm"
include "subrg1cl.mm"
include "subrgmcl.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "3jca.mm"
include "wa.mm"
include "cress.mm"
include "wss.mm"
include "simpl.mm"
include "cplusg.mm"
include "cbs.mm"
include "wceq.mm"
include "simpr1.mm"
include "eqid.mm"
include "subgbas.mm"
include "syl.mm"
include "ressplusg.mm"
include "cmulr.mm"
include "ressmulr.mm"
include "cgrp.mm"
include "subggrp.mm"
include "simpr3.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "syl5com.mm"
include "3impib.mm"
include "subgss.mm"
include "sseld.mm"
include "3anim123d.mm"
include "imp.mm"
include "ringass.mm"
include "adantlr.mm"
include "syldan.mm"
include "ringdi.mm"
include "ringdir.mm"
include "simpr2.mm"
include "ringlidm.mm"
include "ringridm.mm"
include "isringd.mm"
include "jca.mm"
include "issubrg.mm"
include "sylanbrc.mm"
include "ex.mm"
include "impbid2.mm"

theorem issubrg2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume issubrg2.b: |- B = ( Base ` R )
  assume issubrg2.o: |- .1. = ( 1r ` R )
  assume issubrg2.t: |- .x. = ( .r ` R )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint R x
  disjoint R y
  disjoint .x. x
  disjoint .x. y
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint .1. u
  disjoint .1. v
  disjoint .1. w
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint .x. u
  disjoint .x. v
  disjoint .x. w
  assert |- ( R e. Ring -> ( A e. ( SubRing ` R ) <-> ( A e. ( SubGrp ` R ) /\ .1. e. A /\ A. x e. A A. y e. A ( x .x. y ) e. A ) ) )

  proof
    cR
    crg
    wcel
    #
    cA
    cR
    csubrg
    cfv
    wcel
    #
    cA
    cR
    csubg
    cfv
    #
    wcel
    #
    c.1
    cA
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    c.x
    co
    #
    cA
    wcel
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    w3a
    #
    @1
    @3
    @4
    @9
    cA
    cR
    subrgsubg
    cA
    cR
    c.1
    issubrg2.o
    subrg1cl
    @1
    @8
    vx
    vy
    cA
    cA
    @1
    @5
    cA
    wcel
    @6
    cA
    wcel
    @8
    cA
    cR
    c.x
    @5
    @6
    issubrg2.t
    subrgmcl
    3expb
    ralrimivva
    3jca
    @0
    @10
    @1
    @0
    @10
    wa
    #
    @0
    cR
    cA
    cress
    co
    #
    crg
    wcel
    #
    wa
    cA
    cB
    wss
    #
    @4
    wa
    @1
    @11
    @0
    @13
    @0
    @10
    simpl
    @11
    vu
    vv
    vw
    cA
    cR
    cplusg
    cfv
    #
    @12
    c.x
    c.1
    @11
    @3
    cA
    @12
    cbs
    cfv
    wceq
    @0
    @3
    @4
    @9
    simpr1
    #
    cA
    cR
    @12
    @12
    eqid
    #
    subgbas
    syl
    @11
    @3
    @15
    @12
    cplusg
    cfv
    wceq
    @16
    cA
    @15
    cR
    @12
    @2
    @17
    @15
    eqid
    #
    ressplusg
    syl
    @11
    @3
    c.x
    @12
    cmulr
    cfv
    wceq
    @16
    cA
    cR
    @12
    c.x
    @2
    @17
    issubrg2.t
    ressmulr
    syl
    @11
    @3
    @12
    cgrp
    wcel
    @16
    cA
    cR
    @12
    @17
    subggrp
    syl
    @11
    vu
    cv
    #
    cA
    wcel
    #
    vv
    cv
    #
    cA
    wcel
    #
    @19
    @21
    c.x
    co
    #
    cA
    wcel
    #
    @11
    @9
    @20
    @22
    wa
    @24
    @0
    @3
    @4
    @9
    simpr3
    @8
    @24
    @19
    @6
    c.x
    co
    #
    cA
    wcel
    vx
    vy
    @19
    @21
    cA
    cA
    @5
    @19
    wceq
    @7
    @25
    cA
    @5
    @19
    @6
    c.x
    oveq1
    eleq1d
    @6
    @21
    wceq
    @25
    @23
    cA
    @6
    @21
    @19
    c.x
    oveq2
    eleq1d
    rspc2v
    syl5com
    3impib
    @11
    @20
    @22
    vw
    cv
    #
    cA
    wcel
    #
    w3a
    #
    @19
    cB
    wcel
    #
    @21
    cB
    wcel
    #
    @26
    cB
    wcel
    #
    w3a
    #
    @23
    @26
    c.x
    co
    @19
    @21
    @26
    c.x
    co
    #
    c.x
    co
    wceq
    #
    @11
    @28
    @32
    @11
    @20
    @29
    @22
    @30
    @27
    @31
    @11
    cA
    cB
    @19
    @11
    @3
    @14
    @16
    cB
    cA
    cR
    issubrg2.b
    subgss
    syl
    #
    sseld
    #
    @11
    cA
    cB
    @21
    @35
    sseld
    @11
    cA
    cB
    @26
    @35
    sseld
    3anim123d
    imp
    #
    @0
    @32
    @34
    @10
    cB
    cR
    c.x
    @19
    @21
    @26
    issubrg2.b
    issubrg2.t
    ringass
    adantlr
    syldan
    @11
    @28
    @32
    @19
    @21
    @26
    @15
    co
    c.x
    co
    @23
    @19
    @26
    c.x
    co
    #
    @15
    co
    wceq
    #
    @37
    @0
    @32
    @39
    @10
    cB
    @15
    cR
    c.x
    @19
    @21
    @26
    issubrg2.b
    @18
    issubrg2.t
    ringdi
    adantlr
    syldan
    @11
    @28
    @32
    @19
    @21
    @15
    co
    @26
    c.x
    co
    @38
    @33
    @15
    co
    wceq
    #
    @37
    @0
    @32
    @40
    @10
    cB
    @15
    cR
    c.x
    @19
    @21
    @26
    issubrg2.b
    @18
    issubrg2.t
    ringdir
    adantlr
    syldan
    @0
    @3
    @4
    @9
    simpr2
    #
    @11
    @20
    @29
    c.1
    @19
    c.x
    co
    @19
    wceq
    #
    @11
    @20
    @29
    @36
    imp
    #
    @0
    @29
    @42
    @10
    cB
    cR
    c.x
    c.1
    @19
    issubrg2.b
    issubrg2.t
    issubrg2.o
    ringlidm
    adantlr
    syldan
    @11
    @20
    @29
    @19
    c.1
    c.x
    co
    @19
    wceq
    #
    @43
    @0
    @29
    @44
    @10
    cB
    cR
    c.x
    c.1
    @19
    issubrg2.b
    issubrg2.t
    issubrg2.o
    ringridm
    adantlr
    syldan
    isringd
    jca
    @11
    @14
    @4
    @35
    @41
    jca
    cA
    cB
    cR
    c.1
    issubrg2.b
    issubrg2.o
    issubrg
    sylanbrc
    ex
    impbid2
end
