include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "crn.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wb.mm"
include "wral.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "simpr.mm"
include "sseldi.mm"
include "conjnmz.mm"
include "jca.mm"
include "simprl.mm"
include "simplrr.mm"
include "eleq2d.mm"
include "wrex.mm"
include "cgrp.mm"
include "subgrcl.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "wss.mm"
include "subgss.mm"
include "ad2antrr.mm"
include "sselda.mm"
include "grpaddsubass.mm"
include "syl13anc.mm"
include "eqeq1d.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "simplr.mm"
include "grplcan.mm"
include "grpsubadd.mm"
include "3bitrd.mm"
include "eqcom.mm"
include "3bitr4g.mm"
include "rexbidva.mm"
include "adantlrr.mm"
include "ovex.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "rnmpt.mm"
include "elab2.mm"
include "risset.mm"
include "bitrd.mm"
include "ralrimiva.mm"
include "elnmz.mm"
include "sylanbrc.mm"
include "impbida.mm"

theorem conjnmzb
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let c.pl: class .+
  let cS: class S
  let cF: class F
  let cG: class G
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let vw: setvar w
  assume conjghm.x: |- X = ( Base ` G )
  assume conjghm.p: |- .+ = ( +g ` G )
  assume conjghm.m: |- .- = ( -g ` G )
  assume conjsubg.f: |- F = ( x e. S |-> ( ( A .+ x ) .- A ) )
  assume conjnmz.1: |- N = { y e. X | A. z e. X ( ( y .+ z ) e. S <-> ( z .+ y ) e. S ) }

  disjoint x y
  disjoint .- x
  disjoint .- y
  disjoint x z
  disjoint .+ x
  disjoint y z
  disjoint .+ y
  disjoint .+ z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint F y
  disjoint F z
  disjoint N x
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint .+ w
  disjoint A w
  disjoint F w
  disjoint N w
  disjoint G w
  disjoint S w
  disjoint X w
  assert |- ( S e. ( SubGrp ` G ) -> ( A e. N <-> ( A e. X /\ S = ran F ) ) )

  proof
    cS
    cG
    csubg
    cfv
    wcel
    #
    cA
    cN
    wcel
    #
    cA
    cX
    wcel
    #
    cS
    cF
    crn
    #
    wceq
    #
    wa
    #
    @0
    @1
    wa
    #
    @2
    @4
    @6
    cN
    cX
    cA
    cN
    vy
    cv
    #
    vz
    cv
    #
    c.pl
    co
    cS
    wcel
    @8
    @7
    c.pl
    co
    cS
    wcel
    wb
    vz
    cX
    wral
    #
    vy
    cX
    crab
    cX
    conjnmz.1
    @9
    vy
    cX
    ssrab2
    eqsstri
    @0
    @1
    simpr
    sseldi
    vx
    vy
    vz
    cA
    c.pl
    cS
    cF
    cG
    c.mi
    cN
    cX
    conjghm.x
    conjghm.p
    conjghm.m
    conjsubg.f
    conjnmz.1
    conjnmz
    jca
    @0
    @5
    wa
    #
    @2
    cA
    vw
    cv
    #
    c.pl
    co
    #
    cS
    wcel
    #
    @11
    cA
    c.pl
    co
    #
    cS
    wcel
    #
    wb
    #
    vw
    cX
    wral
    @1
    @0
    @2
    @4
    simprl
    @10
    @16
    vw
    cX
    @10
    @11
    cX
    wcel
    #
    wa
    #
    @13
    @12
    @3
    wcel
    #
    @15
    @18
    cS
    @3
    @12
    @0
    @2
    @4
    @17
    simplrr
    eleq2d
    @18
    @12
    cA
    vx
    cv
    #
    c.pl
    co
    cA
    c.mi
    co
    #
    wceq
    #
    vx
    cS
    wrex
    #
    @20
    @14
    wceq
    #
    vx
    cS
    wrex
    #
    @19
    @15
    @0
    @2
    @17
    @23
    @25
    wb
    @4
    @0
    @2
    wa
    #
    @17
    wa
    #
    @22
    @24
    vx
    cS
    @27
    @20
    cS
    wcel
    #
    wa
    #
    @21
    @12
    wceq
    #
    @14
    @20
    wceq
    #
    @22
    @24
    @29
    @30
    cA
    @20
    cA
    c.mi
    co
    #
    c.pl
    co
    #
    @12
    wceq
    #
    @32
    @11
    wceq
    #
    @31
    @29
    @21
    @33
    @12
    @29
    cG
    cgrp
    wcel
    #
    @2
    @20
    cX
    wcel
    #
    @2
    @21
    @33
    wceq
    @0
    @36
    @2
    @17
    @28
    cS
    cG
    subgrcl
    ad3antrrr
    #
    @0
    @2
    @17
    @28
    simpllr
    #
    @27
    cS
    cX
    @20
    @0
    cS
    cX
    wss
    @2
    @17
    cX
    cS
    cG
    conjghm.x
    subgss
    ad2antrr
    sselda
    #
    @39
    cX
    c.pl
    cG
    c.mi
    cA
    @20
    cA
    conjghm.x
    conjghm.p
    conjghm.m
    grpaddsubass
    syl13anc
    eqeq1d
    @29
    @36
    @32
    cX
    wcel
    #
    @17
    @2
    @34
    @35
    wb
    @38
    @29
    @36
    @37
    @2
    @41
    @38
    @40
    @39
    cX
    cG
    c.mi
    @20
    cA
    conjghm.x
    conjghm.m
    grpsubcl
    syl3anc
    @26
    @17
    @28
    simplr
    #
    @39
    cX
    c.pl
    cG
    @32
    @11
    cA
    conjghm.x
    conjghm.p
    grplcan
    syl13anc
    @29
    @36
    @37
    @2
    @17
    @35
    @31
    wb
    @38
    @40
    @39
    @42
    cX
    c.pl
    cG
    c.mi
    @20
    cA
    @11
    conjghm.x
    conjghm.p
    conjghm.m
    grpsubadd
    syl13anc
    3bitrd
    @12
    @21
    eqcom
    @20
    @14
    eqcom
    3bitr4g
    rexbidva
    adantlrr
    @7
    @21
    wceq
    #
    vx
    cS
    wrex
    @23
    vy
    @12
    @3
    cA
    @11
    c.pl
    ovex
    @7
    @12
    wceq
    @43
    @22
    vx
    cS
    @7
    @12
    @21
    eqeq1
    rexbidv
    vx
    vy
    cS
    @21
    cF
    conjsubg.f
    rnmpt
    elab2
    vx
    @14
    cS
    risset
    3bitr4g
    bitrd
    ralrimiva
    vy
    vz
    vw
    cA
    c.pl
    cS
    cN
    cX
    conjnmz.1
    elnmz
    sylanbrc
    impbida
end
