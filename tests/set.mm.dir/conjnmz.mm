include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "cv.mm"
include "cminusg.mm"
include "co.mm"
include "wceq.mm"
include "cgrp.mm"
include "subgrcl.mm"
include "ad2antrr.mm"
include "wb.mm"
include "wral.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "simplr.mm"
include "sseldi.mm"
include "eqid.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "wss.mm"
include "subgss.mm"
include "adantr.mm"
include "sselda.mm"
include "grpass.mm"
include "syl13anc.mm"
include "c0g.mm"
include "grprinv.mm"
include "oveq1d.mm"
include "grplid.mm"
include "3eqtr3d.mm"
include "simpr.mm"
include "eqeltrd.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "nmzbi.mm"
include "mpbid.mm"
include "eqeltrrd.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "grppncan.mm"
include "3eqtrd.mm"
include "wfn.mm"
include "fnmpti.mm"
include "fnfvelrn.mm"
include "sylancr.mm"
include "ex.mm"
include "ssrdv.mm"
include "wf.mm"
include "grpaddsubass.mm"
include "grpnpcan.mm"
include "grpsubcl.mm"
include "mpbird.mm"
include "fmptd.mm"
include "frn.mm"
include "eqssd.mm"

theorem conjnmz
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
  assert |- ( ( S e. ( SubGrp ` G ) /\ A e. N ) -> S = ran F )

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
    wa
    #
    cS
    cF
    crn
    #
    @2
    vw
    cS
    @3
    @2
    vw
    cv
    #
    cS
    wcel
    #
    @4
    @3
    wcel
    @2
    @5
    wa
    #
    cA
    cG
    cminusg
    cfv
    #
    cfv
    #
    @4
    cA
    c.pl
    co
    #
    c.pl
    co
    #
    cF
    cfv
    #
    @4
    @3
    @6
    @11
    cA
    @10
    c.pl
    co
    #
    cA
    c.mi
    co
    #
    @9
    cA
    c.mi
    co
    #
    @4
    @6
    @10
    cS
    wcel
    #
    @11
    @13
    wceq
    @6
    @8
    @4
    c.pl
    co
    #
    cA
    c.pl
    co
    #
    @10
    cS
    @6
    cG
    cgrp
    wcel
    #
    @8
    cX
    wcel
    #
    @4
    cX
    wcel
    #
    cA
    cX
    wcel
    #
    @17
    @10
    wceq
    @0
    @18
    @1
    @5
    cS
    cG
    subgrcl
    #
    ad2antrr
    #
    @6
    @18
    @21
    @19
    @23
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
    @25
    @24
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
    @26
    vy
    cX
    ssrab2
    eqsstri
    #
    @0
    @1
    @5
    simplr
    #
    sseldi
    #
    cX
    cG
    @7
    cA
    conjghm.x
    @7
    eqid
    #
    grpinvcl
    syl2anc
    #
    @2
    cS
    cX
    @4
    @0
    cS
    cX
    wss
    @1
    cX
    cS
    cG
    conjghm.x
    subgss
    adantr
    #
    sselda
    #
    @29
    cX
    c.pl
    cG
    @8
    @4
    cA
    conjghm.x
    conjghm.p
    grpass
    syl13anc
    @6
    cA
    @16
    c.pl
    co
    #
    cS
    wcel
    #
    @17
    cS
    wcel
    #
    @6
    @34
    @4
    cS
    @6
    cA
    @8
    c.pl
    co
    #
    @4
    c.pl
    co
    #
    cG
    c0g
    cfv
    #
    @4
    c.pl
    co
    #
    @34
    @4
    @6
    @37
    @39
    @4
    c.pl
    @6
    @18
    @21
    @37
    @39
    wceq
    @23
    @29
    cX
    c.pl
    cG
    @7
    cA
    @39
    conjghm.x
    conjghm.p
    @39
    eqid
    #
    @30
    grprinv
    syl2anc
    #
    oveq1d
    @6
    @18
    @21
    @19
    @20
    @38
    @34
    wceq
    @23
    @29
    @31
    @33
    cX
    c.pl
    cG
    cA
    @8
    @4
    conjghm.x
    conjghm.p
    grpass
    syl13anc
    @6
    @18
    @20
    @40
    @4
    wceq
    @23
    @33
    cX
    c.pl
    cG
    @4
    @39
    conjghm.x
    conjghm.p
    @41
    grplid
    syl2anc
    3eqtr3d
    @2
    @5
    simpr
    eqeltrd
    @6
    @1
    @16
    cX
    wcel
    #
    @35
    @36
    wb
    @28
    @6
    @18
    @19
    @20
    @43
    @23
    @31
    @33
    cX
    c.pl
    cG
    @8
    @4
    conjghm.x
    conjghm.p
    grpcl
    syl3anc
    vy
    vz
    cA
    @16
    c.pl
    cS
    cN
    cX
    conjnmz.1
    nmzbi
    syl2anc
    mpbid
    eqeltrrd
    #
    vx
    @10
    cA
    vx
    cv
    #
    c.pl
    co
    #
    cA
    c.mi
    co
    #
    @13
    cS
    cF
    @45
    @10
    wceq
    @46
    @12
    cA
    c.mi
    @45
    @10
    cA
    c.pl
    oveq2
    oveq1d
    conjsubg.f
    @12
    cA
    c.mi
    ovex
    fvmpt
    syl
    @6
    @12
    @9
    cA
    c.mi
    @6
    @37
    @9
    c.pl
    co
    #
    @39
    @9
    c.pl
    co
    #
    @12
    @9
    @6
    @37
    @39
    @9
    c.pl
    @42
    oveq1d
    @6
    @18
    @21
    @19
    @9
    cX
    wcel
    #
    @48
    @12
    wceq
    @23
    @29
    @31
    @6
    @18
    @20
    @21
    @50
    @23
    @33
    @29
    cX
    c.pl
    cG
    @4
    cA
    conjghm.x
    conjghm.p
    grpcl
    syl3anc
    #
    cX
    c.pl
    cG
    cA
    @8
    @9
    conjghm.x
    conjghm.p
    grpass
    syl13anc
    @6
    @18
    @50
    @49
    @9
    wceq
    @23
    @51
    cX
    c.pl
    cG
    @9
    @39
    conjghm.x
    conjghm.p
    @41
    grplid
    syl2anc
    3eqtr3d
    oveq1d
    @6
    @18
    @20
    @21
    @14
    @4
    wceq
    @23
    @33
    @29
    cX
    c.pl
    cG
    c.mi
    @4
    cA
    conjghm.x
    conjghm.p
    conjghm.m
    grppncan
    syl3anc
    3eqtrd
    @6
    cF
    cS
    wfn
    @15
    @11
    @3
    wcel
    vx
    cS
    @47
    cF
    @46
    cA
    c.mi
    ovex
    conjsubg.f
    fnmpti
    @44
    cS
    @10
    cF
    fnfvelrn
    sylancr
    eqeltrrd
    ex
    ssrdv
    @2
    cS
    cS
    cF
    wf
    @3
    cS
    wss
    @2
    vx
    cS
    @47
    cS
    cF
    @2
    @45
    cS
    wcel
    #
    wa
    #
    @47
    cA
    @45
    cA
    c.mi
    co
    #
    c.pl
    co
    #
    cS
    @53
    @18
    @21
    @45
    cX
    wcel
    #
    @21
    @47
    @55
    wceq
    @0
    @18
    @1
    @52
    @22
    ad2antrr
    #
    @53
    cN
    cX
    cA
    @27
    @0
    @1
    @52
    simplr
    #
    sseldi
    #
    @2
    cS
    cX
    @45
    @32
    sselda
    #
    @59
    cX
    c.pl
    cG
    c.mi
    cA
    @45
    cA
    conjghm.x
    conjghm.p
    conjghm.m
    grpaddsubass
    syl13anc
    @53
    @55
    cS
    wcel
    #
    @54
    cA
    c.pl
    co
    #
    cS
    wcel
    #
    @53
    @62
    @45
    cS
    @53
    @18
    @56
    @21
    @62
    @45
    wceq
    @57
    @60
    @59
    cX
    c.pl
    cG
    c.mi
    @45
    cA
    conjghm.x
    conjghm.p
    conjghm.m
    grpnpcan
    syl3anc
    @2
    @52
    simpr
    eqeltrd
    @53
    @1
    @54
    cX
    wcel
    #
    @61
    @63
    wb
    @58
    @53
    @18
    @56
    @21
    @64
    @57
    @60
    @59
    cX
    cG
    c.mi
    @45
    cA
    conjghm.x
    conjghm.m
    grpsubcl
    syl3anc
    vy
    vz
    cA
    @54
    c.pl
    cS
    cN
    cX
    conjnmz.1
    nmzbi
    syl2anc
    mpbird
    eqeltrd
    conjsubg.f
    fmptd
    cS
    cS
    cF
    frn
    syl
    eqssd
end
