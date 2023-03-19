include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "cghm.mm"
include "co.mm"
include "wf1o.mm"
include "simpl.mm"
include "cv.mm"
include "adantr.mm"
include "grpcl.mm"
include "3expa.mm"
include "simplr.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "fmptd.mm"
include "cfv.mm"
include "wceq.mm"
include "simprl.mm"
include "simprr.mm"
include "grpass.mm"
include "syl13anc.mm"
include "grpnpcan.mm"
include "oveq1d.mm"
include "grpaddsubass.mm"
include "3eqtr2rd.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "oveq12d.mm"
include "isghmd.mm"
include "cminusg.mm"
include "eqid.mm"
include "grpinvcl.mm"
include "simpr.mm"
include "wb.mm"
include "adantrl.mm"
include "adantrr.mm"
include "grplcan.mm"
include "c0g.mm"
include "grplinv.mm"
include "grplid.mm"
include "ad2ant2r.mm"
include "3eqtr3rd.mm"
include "eqeq2d.mm"
include "grpsubadd.mm"
include "3bitr4d.mm"
include "eqcom.mm"
include "3bitr4g.mm"
include "f1o2d.mm"
include "jca.mm"

theorem conjghm
  let vx: setvar x
  let cA: class A
  let c.pl: class .+
  let cF: class F
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  let cN: class N
  let cS: class S
  assume conjghm.x: |- X = ( Base ` G )
  assume conjghm.p: |- .+ = ( +g ` G )
  assume conjghm.m: |- .- = ( -g ` G )
  assume conjghm.f: |- F = ( x e. X |-> ( ( A .+ x ) .- A ) )

  disjoint .- x
  disjoint .+ x
  disjoint A x
  disjoint G x
  disjoint X x
  disjoint x y
  disjoint .- y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint .+ w
  disjoint x z
  disjoint y z
  disjoint .+ y
  disjoint .+ z
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint N w
  disjoint N x
  disjoint G w
  disjoint G y
  disjoint G z
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint X w
  disjoint X y
  disjoint X z
  assert |- ( ( G e. Grp /\ A e. X ) -> ( F e. ( G GrpHom G ) /\ F : X -1-1-onto-> X ) )

  proof
    cG
    cgrp
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cF
    cG
    cG
    cghm
    co
    wcel
    cX
    cX
    cF
    wf1o
    @2
    vy
    vz
    c.pl
    c.pl
    cG
    cG
    cF
    cX
    cX
    conjghm.x
    conjghm.x
    conjghm.p
    conjghm.p
    @0
    @1
    simpl
    #
    @3
    @2
    vx
    cX
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
    cX
    cF
    @2
    @4
    cX
    wcel
    #
    wa
    @0
    @5
    cX
    wcel
    #
    @1
    @6
    cX
    wcel
    @2
    @0
    @7
    @3
    adantr
    @0
    @1
    @7
    @8
    cX
    c.pl
    cG
    cA
    @4
    conjghm.x
    conjghm.p
    grpcl
    3expa
    #
    @0
    @1
    @7
    simplr
    cX
    cG
    c.mi
    @5
    cA
    conjghm.x
    conjghm.m
    grpsubcl
    syl3anc
    #
    conjghm.f
    fmptd
    @2
    vy
    cv
    #
    cX
    wcel
    #
    vz
    cv
    #
    cX
    wcel
    #
    wa
    #
    wa
    #
    cA
    @11
    @13
    c.pl
    co
    #
    c.pl
    co
    #
    cA
    c.mi
    co
    #
    cA
    @11
    c.pl
    co
    #
    cA
    c.mi
    co
    #
    cA
    @13
    c.pl
    co
    #
    cA
    c.mi
    co
    #
    c.pl
    co
    #
    @17
    cF
    cfv
    #
    @11
    cF
    cfv
    #
    @13
    cF
    cfv
    #
    c.pl
    co
    @16
    @21
    cA
    c.pl
    co
    #
    @13
    cA
    c.mi
    co
    #
    c.pl
    co
    #
    @21
    cA
    @29
    c.pl
    co
    #
    c.pl
    co
    #
    @19
    @24
    @16
    @0
    @21
    cX
    wcel
    #
    @1
    @29
    cX
    wcel
    #
    @30
    @32
    wceq
    @2
    @0
    @15
    @3
    adantr
    #
    @16
    @0
    @20
    cX
    wcel
    #
    @1
    @33
    @35
    @16
    @0
    @1
    @12
    @36
    @35
    @0
    @1
    @15
    simplr
    #
    @2
    @12
    @14
    simprl
    #
    cX
    c.pl
    cG
    cA
    @11
    conjghm.x
    conjghm.p
    grpcl
    syl3anc
    #
    @37
    cX
    cG
    c.mi
    @20
    cA
    conjghm.x
    conjghm.m
    grpsubcl
    syl3anc
    @37
    @16
    @0
    @14
    @1
    @34
    @35
    @2
    @12
    @14
    simprr
    #
    @37
    cX
    cG
    c.mi
    @13
    cA
    conjghm.x
    conjghm.m
    grpsubcl
    syl3anc
    cX
    c.pl
    cG
    @21
    cA
    @29
    conjghm.x
    conjghm.p
    grpass
    syl13anc
    @16
    @30
    @20
    @29
    c.pl
    co
    #
    @20
    @13
    c.pl
    co
    #
    cA
    c.mi
    co
    #
    @19
    @16
    @28
    @20
    @29
    c.pl
    @16
    @0
    @36
    @1
    @28
    @20
    wceq
    @35
    @39
    @37
    cX
    c.pl
    cG
    c.mi
    @20
    cA
    conjghm.x
    conjghm.p
    conjghm.m
    grpnpcan
    syl3anc
    oveq1d
    @16
    @0
    @36
    @14
    @1
    @43
    @41
    wceq
    @35
    @39
    @40
    @37
    cX
    c.pl
    cG
    c.mi
    @20
    @13
    cA
    conjghm.x
    conjghm.p
    conjghm.m
    grpaddsubass
    syl13anc
    @16
    @42
    @18
    cA
    c.mi
    @16
    @0
    @1
    @12
    @14
    @42
    @18
    wceq
    @35
    @37
    @38
    @40
    cX
    c.pl
    cG
    cA
    @11
    @13
    conjghm.x
    conjghm.p
    grpass
    syl13anc
    oveq1d
    3eqtr2rd
    @16
    @23
    @31
    @21
    c.pl
    @16
    @0
    @1
    @14
    @1
    @23
    @31
    wceq
    @35
    @37
    @40
    @37
    cX
    c.pl
    cG
    c.mi
    cA
    @13
    cA
    conjghm.x
    conjghm.p
    conjghm.m
    grpaddsubass
    syl13anc
    oveq2d
    3eqtr4d
    @16
    @17
    cX
    wcel
    #
    @25
    @19
    wceq
    @16
    @0
    @12
    @14
    @44
    @35
    @38
    @40
    cX
    c.pl
    cG
    @11
    @13
    conjghm.x
    conjghm.p
    grpcl
    syl3anc
    vx
    @17
    @6
    @19
    cX
    cF
    @4
    @17
    wceq
    @5
    @18
    cA
    c.mi
    @4
    @17
    cA
    c.pl
    oveq2
    oveq1d
    conjghm.f
    @18
    cA
    c.mi
    ovex
    fvmpt
    syl
    @16
    @26
    @21
    @27
    @23
    c.pl
    @12
    @26
    @21
    wceq
    @2
    @14
    vx
    @11
    @6
    @21
    cX
    cF
    @4
    @11
    wceq
    @5
    @20
    cA
    c.mi
    @4
    @11
    cA
    c.pl
    oveq2
    oveq1d
    conjghm.f
    @20
    cA
    c.mi
    ovex
    fvmpt
    ad2antrl
    @14
    @27
    @23
    wceq
    @2
    @12
    vx
    @13
    @6
    @23
    cX
    cF
    @4
    @13
    wceq
    @5
    @22
    cA
    c.mi
    @4
    @13
    cA
    c.pl
    oveq2
    oveq1d
    conjghm.f
    @22
    cA
    c.mi
    ovex
    fvmpt
    ad2antll
    oveq12d
    3eqtr4d
    isghmd
    @2
    vx
    vy
    cX
    cX
    @6
    cA
    cG
    cminusg
    cfv
    #
    cfv
    #
    @11
    cA
    c.pl
    co
    #
    c.pl
    co
    #
    cF
    conjghm.f
    @10
    @2
    @12
    wa
    #
    @0
    @46
    cX
    wcel
    #
    @47
    cX
    wcel
    #
    @48
    cX
    wcel
    @2
    @0
    @12
    @3
    adantr
    #
    @2
    @50
    @12
    cX
    cG
    @45
    cA
    conjghm.x
    @45
    eqid
    #
    grpinvcl
    #
    adantr
    @49
    @0
    @12
    @1
    @51
    @52
    @2
    @12
    simpr
    @0
    @1
    @12
    simplr
    cX
    c.pl
    cG
    @11
    cA
    conjghm.x
    conjghm.p
    grpcl
    syl3anc
    #
    cX
    c.pl
    cG
    @46
    @47
    conjghm.x
    conjghm.p
    grpcl
    syl3anc
    @2
    @7
    @12
    wa
    #
    wa
    #
    @48
    @4
    wceq
    #
    @6
    @11
    wceq
    #
    @4
    @48
    wceq
    @11
    @6
    wceq
    @57
    @48
    @46
    @5
    c.pl
    co
    #
    wceq
    #
    @47
    @5
    wceq
    #
    @58
    @59
    @57
    @0
    @51
    @8
    @50
    @61
    @62
    wb
    @2
    @0
    @56
    @3
    adantr
    #
    @2
    @12
    @51
    @7
    @55
    adantrl
    @2
    @7
    @8
    @12
    @9
    adantrr
    #
    @2
    @50
    @56
    @54
    adantr
    #
    cX
    c.pl
    cG
    @47
    @5
    @46
    conjghm.x
    conjghm.p
    grplcan
    syl13anc
    @57
    @4
    @60
    @48
    @57
    @46
    cA
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
    @60
    @4
    @57
    @66
    @68
    @4
    c.pl
    @2
    @66
    @68
    wceq
    @56
    cX
    c.pl
    cG
    @45
    cA
    @68
    conjghm.x
    conjghm.p
    @68
    eqid
    #
    @53
    grplinv
    adantr
    oveq1d
    @57
    @0
    @50
    @1
    @7
    @67
    @60
    wceq
    @63
    @65
    @0
    @1
    @56
    simplr
    #
    @2
    @7
    @12
    simprl
    cX
    c.pl
    cG
    @46
    cA
    @4
    conjghm.x
    conjghm.p
    grpass
    syl13anc
    @0
    @7
    @69
    @4
    wceq
    @1
    @12
    cX
    c.pl
    cG
    @4
    @68
    conjghm.x
    conjghm.p
    @70
    grplid
    ad2ant2r
    3eqtr3rd
    eqeq2d
    @57
    @0
    @8
    @1
    @12
    @59
    @62
    wb
    @63
    @64
    @71
    @2
    @7
    @12
    simprr
    cX
    c.pl
    cG
    c.mi
    @5
    cA
    @11
    conjghm.x
    conjghm.p
    conjghm.m
    grpsubadd
    syl13anc
    3bitr4d
    @4
    @48
    eqcom
    @11
    @6
    eqcom
    3bitr4g
    f1o2d
    jca
end
