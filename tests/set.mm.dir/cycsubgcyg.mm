include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "cress.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "cmg.mm"
include "eqid.mm"
include "csubg.mm"
include "cz.mm"
include "cv.mm"
include "cmpt.mm"
include "crn.mm"
include "cycsubgcl.mm"
include "simpld.mm"
include "syl5eqel.mm"
include "subggrp.mm"
include "syl.mm"
include "simprd.mm"
include "syl6eleqr.mm"
include "wceq.mm"
include "subgbas.mm"
include "eleqtrd.mm"
include "wrex.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "oveq1.mm"
include "cbvmptv.mm"
include "ovex.mm"
include "elrnmpti.mm"
include "sylib.mm"
include "ad2antrr.mm"
include "subgmulg.mm"
include "syl3anc.mm"
include "eqeq2d.mm"
include "rexbidva.mm"
include "mpbid.mm"
include "syldan.mm"
include "iscygd.mm"

theorem cycsubgcyg
  let vx: setvar x
  let cA: class A
  let cS: class S
  let c.x: class .x.
  let cG: class G
  let cX: class X
  let vn: setvar n
  let vy: setvar y
  let vf: setvar f
  let cH: class H
  assume cycsubgcyg.x: |- X = ( Base ` G )
  assume cycsubgcyg.t: |- .x. = ( .g ` G )
  assume cycsubgcyg.s: |- S = ran ( x e. ZZ |-> ( x .x. A ) )

  disjoint A x
  disjoint G x
  disjoint .x. x
  disjoint X x
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A y
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint G f
  disjoint G n
  disjoint G y
  disjoint S n
  disjoint S y
  disjoint .x. n
  disjoint X n
  disjoint X y
  disjoint H f
  assert |- ( ( G e. Grp /\ A e. X ) -> ( G |`s S ) e. CycGrp )

  proof
    cG
    cgrp
    wcel
    cA
    cX
    wcel
    wa
    #
    vy
    cG
    cS
    cress
    co
    #
    cbs
    cfv
    #
    @1
    cmg
    cfv
    #
    vn
    @1
    cA
    @2
    eqid
    @3
    eqid
    #
    @0
    cS
    cG
    csubg
    cfv
    #
    wcel
    #
    @1
    cgrp
    wcel
    @0
    cS
    vx
    cz
    vx
    cv
    #
    cA
    c.x
    co
    #
    cmpt
    #
    crn
    #
    @5
    cycsubgcyg.s
    @0
    @10
    @5
    wcel
    #
    cA
    @10
    wcel
    #
    vx
    cA
    c.x
    @9
    cG
    cX
    cycsubgcyg.x
    cycsubgcyg.t
    @9
    eqid
    cycsubgcl
    #
    simpld
    syl5eqel
    #
    cS
    cG
    @1
    @1
    eqid
    #
    subggrp
    syl
    @0
    cA
    cS
    @2
    @0
    cA
    @10
    cS
    @0
    @11
    @12
    @13
    simprd
    cycsubgcyg.s
    syl6eleqr
    #
    @0
    @6
    cS
    @2
    wceq
    @14
    cS
    cG
    @1
    @15
    subgbas
    syl
    #
    eleqtrd
    @0
    vy
    cv
    #
    @2
    wcel
    #
    @18
    cS
    wcel
    #
    @18
    vn
    cv
    #
    cA
    @3
    co
    #
    wceq
    #
    vn
    cz
    wrex
    #
    @0
    @20
    @19
    @0
    cS
    @2
    @18
    @17
    eleq2d
    biimpar
    @0
    @20
    wa
    #
    @18
    @21
    cA
    c.x
    co
    #
    wceq
    #
    vn
    cz
    wrex
    #
    @24
    @25
    @18
    @10
    wcel
    @28
    @25
    @18
    cS
    @10
    @0
    @20
    simpr
    cycsubgcyg.s
    syl6eleq
    vn
    cz
    @26
    @18
    @9
    vx
    vn
    cz
    @8
    @26
    @7
    @21
    cA
    c.x
    oveq1
    cbvmptv
    @21
    cA
    c.x
    ovex
    elrnmpti
    sylib
    @25
    @27
    @23
    vn
    cz
    @25
    @21
    cz
    wcel
    #
    wa
    #
    @26
    @22
    @18
    @30
    @6
    @29
    cA
    cS
    wcel
    #
    @26
    @22
    wceq
    @0
    @6
    @20
    @29
    @14
    ad2antrr
    @25
    @29
    simpr
    @0
    @31
    @20
    @29
    @16
    ad2antrr
    cS
    @3
    c.x
    cG
    @1
    @21
    cA
    cycsubgcyg.t
    @15
    @4
    subgmulg
    syl3anc
    eqeq2d
    rexbidva
    mpbid
    syldan
    iscygd
end
