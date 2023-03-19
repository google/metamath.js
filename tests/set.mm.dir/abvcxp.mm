include "wcel.mm"
include "cc0.mm"
include "c1.mm"
include "cioc.mm"
include "co.mm"
include "wa.mm"
include "cplusg.mm"
include "cfv.mm"
include "cmulr.mm"
include "c0g.mm"
include "cabv.mm"
include "wceq.mm"
include "a1i.mm"
include "cbs.mm"
include "eqidd.mm"
include "crg.mm"
include "abvrcl.mm"
include "adantr.mm"
include "cv.mm"
include "ccxp.mm"
include "cr.mm"
include "abvcl.mm"
include "adantlr.mm"
include "cle.mm"
include "wbr.mm"
include "abvge0.mm"
include "clt.mm"
include "w3a.mm"
include "simpr.mm"
include "cxr.mm"
include "wb.mm"
include "0xr.mm"
include "1re.mm"
include "elioc2.mm"
include "mp2an.mm"
include "sylib.mm"
include "simp1d.mm"
include "recxpcld.mm"
include "fmptd.mm"
include "eqid.mm"
include "ring0cl.mm"
include "syl.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "abv0.mm"
include "recnd.mm"
include "simp2d.mm"
include "gt0ne0d.mm"
include "0cxpd.mm"
include "eqtrd.mm"
include "wne.mm"
include "simp1l.mm"
include "simp2.mm"
include "syl2anc.mm"
include "abvgt0.mm"
include "3adant1r.mm"
include "elrpd.mm"
include "3ad2ant1.mm"
include "rpcxpcld.mm"
include "rpgt0d.mm"
include "breqtrrd.mm"
include "cmul.mm"
include "simp2l.mm"
include "simp3l.mm"
include "abvmul.mm"
include "syl3anc.mm"
include "cc.mm"
include "mulcxpd.mm"
include "ringcl.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "caddc.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "grpcl.mm"
include "readdcld.mm"
include "addge0d.mm"
include "abvtri.mm"
include "cxple2d.mm"
include "mpbid.mm"
include "simp3d.mm"
include "cxpaddle.mm"
include "letrd.mm"
include "3brtr4d.mm"
include "isabvd.mm"

theorem abvcxp
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let vy: setvar y
  let vz: setvar z
  assume abvcxp.a: |- A = ( AbsVal ` R )
  assume abvcxp.b: |- B = ( Base ` R )
  assume abvcxp.f: |- G = ( x e. B |-> ( ( F ` x ) ^c S ) )

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint R x
  disjoint S x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint F y
  disjoint F z
  disjoint R y
  disjoint R z
  disjoint S y
  disjoint S z
  disjoint G y
  disjoint G z
  assert |- ( ( F e. A /\ S e. ( 0 (,] 1 ) ) -> G e. A )

  proof
    cF
    cA
    wcel
    #
    cS
    cc0
    c1
    cioc
    co
    wcel
    #
    wa
    #
    vy
    vz
    cA
    cB
    cR
    cplusg
    cfv
    #
    cR
    cR
    cmulr
    cfv
    #
    cG
    cR
    c0g
    cfv
    #
    cA
    cR
    cabv
    cfv
    wceq
    @2
    abvcxp.a
    a1i
    cB
    cR
    cbs
    cfv
    wceq
    @2
    abvcxp.b
    a1i
    @2
    @3
    eqidd
    @2
    @4
    eqidd
    @2
    @5
    eqidd
    @0
    cR
    crg
    wcel
    #
    @1
    cA
    cR
    cF
    abvcxp.a
    abvrcl
    adantr
    #
    @2
    vx
    cB
    vx
    cv
    #
    cF
    cfv
    #
    cS
    ccxp
    co
    #
    cr
    cG
    @2
    @8
    cB
    wcel
    #
    wa
    @9
    cS
    @0
    @11
    @9
    cr
    wcel
    @1
    cA
    cB
    cR
    cF
    @8
    abvcxp.a
    abvcxp.b
    abvcl
    adantlr
    @0
    @11
    cc0
    @9
    cle
    wbr
    @1
    cA
    cB
    cR
    cF
    @8
    abvcxp.a
    abvcxp.b
    abvge0
    adantlr
    @2
    cS
    cr
    wcel
    #
    @11
    @2
    @12
    cc0
    cS
    clt
    wbr
    #
    cS
    c1
    cle
    wbr
    #
    @2
    @1
    @12
    @13
    @14
    w3a
    #
    @0
    @1
    simpr
    cc0
    cxr
    wcel
    c1
    cr
    wcel
    @1
    @15
    wb
    0xr
    1re
    cc0
    c1
    cS
    elioc2
    mp2an
    sylib
    #
    simp1d
    #
    adantr
    recxpcld
    abvcxp.f
    fmptd
    @2
    @5
    cG
    cfv
    #
    @5
    cF
    cfv
    #
    cS
    ccxp
    co
    #
    cc0
    @2
    @5
    cB
    wcel
    #
    @18
    @20
    wceq
    @2
    @6
    @21
    @7
    cB
    cR
    @5
    abvcxp.b
    @5
    eqid
    #
    ring0cl
    syl
    vx
    @5
    @10
    @20
    cB
    cG
    @8
    @5
    wceq
    @9
    @19
    cS
    ccxp
    @8
    @5
    cF
    fveq2
    oveq1d
    abvcxp.f
    @19
    cS
    ccxp
    ovex
    fvmpt
    syl
    @2
    @20
    cc0
    cS
    ccxp
    co
    cc0
    @2
    @19
    cc0
    cS
    ccxp
    @0
    @19
    cc0
    wceq
    @1
    cA
    cR
    cF
    @5
    abvcxp.a
    @22
    abv0
    adantr
    oveq1d
    @2
    cS
    @2
    cS
    @17
    recnd
    #
    @2
    cS
    @2
    @12
    @13
    @14
    @16
    simp2d
    gt0ne0d
    0cxpd
    eqtrd
    eqtrd
    @2
    vy
    cv
    #
    cB
    wcel
    #
    @24
    @5
    wne
    #
    w3a
    #
    cc0
    @24
    cF
    cfv
    #
    cS
    ccxp
    co
    #
    @24
    cG
    cfv
    #
    clt
    @27
    @29
    @27
    @28
    cS
    @27
    @28
    @27
    @0
    @25
    @28
    cr
    wcel
    #
    @0
    @1
    @25
    @26
    simp1l
    @2
    @25
    @26
    simp2
    #
    cA
    cB
    cR
    cF
    @24
    abvcxp.a
    abvcxp.b
    abvcl
    #
    syl2anc
    @0
    @25
    @26
    cc0
    @28
    clt
    wbr
    @1
    cA
    cB
    cR
    cF
    @24
    @5
    abvcxp.a
    abvcxp.b
    @22
    abvgt0
    3adant1r
    elrpd
    @2
    @25
    @12
    @26
    @17
    3ad2ant1
    rpcxpcld
    rpgt0d
    @27
    @25
    @30
    @29
    wceq
    #
    @32
    vx
    @24
    @10
    @29
    cB
    cG
    @8
    @24
    wceq
    @9
    @28
    cS
    ccxp
    @8
    @24
    cF
    fveq2
    oveq1d
    abvcxp.f
    @28
    cS
    ccxp
    ovex
    fvmpt
    #
    syl
    breqtrrd
    @2
    @25
    @26
    wa
    #
    vz
    cv
    #
    cB
    wcel
    #
    @37
    @5
    wne
    #
    wa
    #
    w3a
    #
    @24
    @37
    @4
    co
    #
    cF
    cfv
    #
    cS
    ccxp
    co
    #
    @29
    @37
    cF
    cfv
    #
    cS
    ccxp
    co
    #
    cmul
    co
    #
    @42
    cG
    cfv
    #
    @30
    @37
    cG
    cfv
    #
    cmul
    co
    @41
    @44
    @28
    @45
    cmul
    co
    #
    cS
    ccxp
    co
    @47
    @41
    @43
    @50
    cS
    ccxp
    @41
    @0
    @25
    @38
    @43
    @50
    wceq
    @0
    @1
    @36
    @40
    simp1l
    #
    @2
    @25
    @26
    @40
    simp2l
    #
    @2
    @36
    @38
    @39
    simp3l
    #
    cA
    cB
    cR
    @4
    cF
    @24
    @37
    abvcxp.a
    abvcxp.b
    @4
    eqid
    #
    abvmul
    syl3anc
    oveq1d
    @41
    @28
    @45
    cS
    @41
    @0
    @25
    @31
    @51
    @52
    @33
    syl2anc
    #
    @41
    @0
    @25
    cc0
    @28
    cle
    wbr
    @51
    @52
    cA
    cB
    cR
    cF
    @24
    abvcxp.a
    abvcxp.b
    abvge0
    syl2anc
    #
    @41
    @0
    @38
    @45
    cr
    wcel
    @51
    @53
    cA
    cB
    cR
    cF
    @37
    abvcxp.a
    abvcxp.b
    abvcl
    syl2anc
    #
    @41
    @0
    @38
    cc0
    @45
    cle
    wbr
    @51
    @53
    cA
    cB
    cR
    cF
    @37
    abvcxp.a
    abvcxp.b
    abvge0
    syl2anc
    #
    @2
    @36
    cS
    cc
    wcel
    @40
    @23
    3ad2ant1
    mulcxpd
    eqtrd
    @41
    @42
    cB
    wcel
    #
    @48
    @44
    wceq
    @41
    @6
    @25
    @38
    @59
    @2
    @36
    @6
    @40
    @7
    3ad2ant1
    #
    @52
    @53
    cB
    cR
    @4
    @24
    @37
    abvcxp.b
    @54
    ringcl
    syl3anc
    vx
    @42
    @10
    @44
    cB
    cG
    @8
    @42
    wceq
    @9
    @43
    cS
    ccxp
    @8
    @42
    cF
    fveq2
    oveq1d
    abvcxp.f
    @43
    cS
    ccxp
    ovex
    fvmpt
    syl
    @41
    @30
    @29
    @49
    @46
    cmul
    @41
    @25
    @34
    @52
    @35
    syl
    #
    @41
    @38
    @49
    @46
    wceq
    @53
    vx
    @37
    @10
    @46
    cB
    cG
    @8
    @37
    wceq
    @9
    @45
    cS
    ccxp
    @8
    @37
    cF
    fveq2
    oveq1d
    abvcxp.f
    @45
    cS
    ccxp
    ovex
    fvmpt
    syl
    #
    oveq12d
    3eqtr4d
    @41
    @24
    @37
    @3
    co
    #
    cF
    cfv
    #
    cS
    ccxp
    co
    #
    @29
    @46
    caddc
    co
    #
    @63
    cG
    cfv
    #
    @30
    @49
    caddc
    co
    cle
    @41
    @65
    @28
    @45
    caddc
    co
    #
    cS
    ccxp
    co
    #
    @66
    @41
    @64
    cS
    @41
    @0
    @63
    cB
    wcel
    #
    @64
    cr
    wcel
    @51
    @41
    cR
    cgrp
    wcel
    #
    @25
    @38
    @70
    @41
    @6
    @71
    @60
    cR
    ringgrp
    syl
    @52
    @53
    cB
    @3
    cR
    @24
    @37
    abvcxp.b
    @3
    eqid
    #
    grpcl
    syl3anc
    #
    cA
    cB
    cR
    cF
    @63
    abvcxp.a
    abvcxp.b
    abvcl
    syl2anc
    #
    @41
    @0
    @70
    cc0
    @64
    cle
    wbr
    @51
    @73
    cA
    cB
    cR
    cF
    @63
    abvcxp.a
    abvcxp.b
    abvge0
    syl2anc
    #
    @41
    @12
    @13
    @14
    @2
    @36
    @15
    @40
    @16
    3ad2ant1
    #
    simp1d
    #
    recxpcld
    @41
    @68
    cS
    @41
    @28
    @45
    @55
    @57
    readdcld
    #
    @41
    @28
    @45
    @55
    @57
    @56
    @58
    addge0d
    #
    @77
    recxpcld
    @41
    @29
    @46
    @41
    @28
    cS
    @55
    @56
    @77
    recxpcld
    @41
    @45
    cS
    @57
    @58
    @77
    recxpcld
    readdcld
    @41
    @64
    @68
    cle
    wbr
    #
    @65
    @69
    cle
    wbr
    @41
    @0
    @25
    @38
    @80
    @51
    @52
    @53
    cA
    cB
    @3
    cR
    cF
    @24
    @37
    abvcxp.a
    abvcxp.b
    @72
    abvtri
    syl3anc
    @41
    @64
    @68
    cS
    @74
    @75
    @78
    @79
    @41
    cS
    @77
    @41
    @12
    @13
    @14
    @76
    simp2d
    elrpd
    #
    cxple2d
    mpbid
    @41
    @28
    @45
    cS
    @55
    @56
    @57
    @58
    @81
    @41
    @12
    @13
    @14
    @76
    simp3d
    cxpaddle
    letrd
    @41
    @70
    @67
    @65
    wceq
    @73
    vx
    @63
    @10
    @65
    cB
    cG
    @8
    @63
    wceq
    @9
    @64
    cS
    ccxp
    @8
    @63
    cF
    fveq2
    oveq1d
    abvcxp.f
    @64
    cS
    ccxp
    ovex
    fvmpt
    syl
    @41
    @30
    @29
    @49
    @46
    caddc
    @61
    @62
    oveq12d
    3brtr4d
    isabvd
end
