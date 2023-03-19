include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "co.mm"
include "wb.mm"
include "wral.mm"
include "subgss.mm"
include "sselda.mm"
include "simpll.mm"
include "cminusg.mm"
include "c0g.mm"
include "cgrp.mm"
include "wceq.mm"
include "subgrcl.mm"
include "syl.mm"
include "wss.mm"
include "simplrl.mm"
include "sseldd.mm"
include "eqid.mm"
include "grplinv.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "subginvcl.mm"
include "simplrr.mm"
include "grpass.mm"
include "syl13anc.mm"
include "grplid.mm"
include "3eqtr3d.mm"
include "simpr.mm"
include "subgcl.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"
include "csg.mm"
include "grppncan.mm"
include "subgsubcl.mm"
include "impbida.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "elnmz.mm"
include "sylanbrc.mm"
include "ex.mm"
include "ssrdv.mm"

theorem ssnmz
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
  assert |- ( S e. ( SubGrp ` G ) -> S C_ N )

  proof
    cS
    cG
    csubg
    cfv
    wcel
    #
    vz
    cS
    cN
    @0
    vz
    cv
    #
    cS
    wcel
    #
    @1
    cN
    wcel
    #
    @0
    @2
    wa
    #
    @1
    cX
    wcel
    #
    @1
    vw
    cv
    #
    c.pl
    co
    #
    cS
    wcel
    #
    @6
    @1
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
    @3
    @0
    cS
    cX
    @1
    cX
    cS
    cG
    nmzsubg.2
    subgss
    #
    sselda
    #
    @4
    @11
    vw
    cX
    @0
    @2
    @6
    cX
    wcel
    #
    @11
    @0
    @2
    @14
    wa
    #
    wa
    #
    @8
    @10
    @16
    @8
    wa
    #
    @0
    @6
    cS
    wcel
    #
    @2
    @10
    @0
    @15
    @8
    simpll
    #
    @17
    @1
    cG
    cminusg
    cfv
    #
    cfv
    #
    @7
    c.pl
    co
    #
    @6
    cS
    @17
    @21
    @1
    c.pl
    co
    #
    @6
    c.pl
    co
    #
    cG
    c0g
    cfv
    #
    @6
    c.pl
    co
    #
    @22
    @6
    @17
    @23
    @25
    @6
    c.pl
    @17
    cG
    cgrp
    wcel
    #
    @5
    @23
    @25
    wceq
    @17
    @0
    @27
    @19
    cS
    cG
    subgrcl
    #
    syl
    #
    @17
    cS
    cX
    @1
    @17
    @0
    cS
    cX
    wss
    @19
    @12
    syl
    #
    @0
    @2
    @14
    @8
    simplrl
    #
    sseldd
    #
    cX
    c.pl
    cG
    @20
    @1
    @25
    nmzsubg.2
    nmzsubg.3
    @25
    eqid
    #
    @20
    eqid
    #
    grplinv
    syl2anc
    oveq1d
    @17
    @27
    @21
    cX
    wcel
    @5
    @14
    @24
    @22
    wceq
    @29
    @17
    cS
    cX
    @21
    @30
    @17
    @0
    @2
    @21
    cS
    wcel
    #
    @19
    @31
    cS
    cG
    @20
    @1
    @34
    subginvcl
    syl2anc
    #
    sseldd
    @32
    @0
    @2
    @14
    @8
    simplrr
    #
    cX
    c.pl
    cG
    @21
    @1
    @6
    nmzsubg.2
    nmzsubg.3
    grpass
    syl13anc
    @17
    @27
    @14
    @26
    @6
    wceq
    @29
    @37
    cX
    c.pl
    cG
    @6
    @25
    nmzsubg.2
    nmzsubg.3
    @33
    grplid
    syl2anc
    3eqtr3d
    @17
    @0
    @35
    @8
    @22
    cS
    wcel
    @19
    @36
    @16
    @8
    simpr
    c.pl
    cS
    cG
    @21
    @7
    nmzsubg.3
    subgcl
    syl3anc
    eqeltrrd
    @31
    c.pl
    cS
    cG
    @6
    @1
    nmzsubg.3
    subgcl
    syl3anc
    @16
    @10
    wa
    #
    @0
    @2
    @18
    @8
    @0
    @15
    @10
    simpll
    #
    @0
    @2
    @14
    @10
    simplrl
    #
    @38
    @9
    @1
    cG
    csg
    cfv
    #
    co
    #
    @6
    cS
    @38
    @27
    @14
    @5
    @42
    @6
    wceq
    @38
    @0
    @27
    @39
    @28
    syl
    @0
    @2
    @14
    @10
    simplrr
    @38
    @0
    @2
    @5
    @39
    @40
    @13
    syl2anc
    cX
    c.pl
    cG
    @41
    @6
    @1
    nmzsubg.2
    nmzsubg.3
    @41
    eqid
    #
    grppncan
    syl3anc
    @38
    @0
    @10
    @2
    @42
    cS
    wcel
    @39
    @16
    @10
    simpr
    @40
    cS
    cG
    @41
    @9
    @1
    @43
    subgsubcl
    syl3anc
    eqeltrrd
    c.pl
    cS
    cG
    @1
    @6
    nmzsubg.3
    subgcl
    syl3anc
    impbida
    anassrs
    ralrimiva
    vx
    vy
    vw
    @1
    c.pl
    cS
    cN
    cX
    elnmz.1
    elnmz
    sylanbrc
    ex
    ssrdv
end
