include "cga.mm"
include "co.mm"
include "wcel.mm"
include "cplusg.mm"
include "cfv.mm"
include "cbs.mm"
include "eqid.mm"
include "gagrp.mm"
include "cvv.mm"
include "cgrp.mm"
include "gaset.mm"
include "symggrp.mm"
include "syl.mm"
include "cv.mm"
include "cmpt.mm"
include "wa.mm"
include "wf1o.mm"
include "gapm.mm"
include "wb.mm"
include "adantr.mm"
include "elsymgbas.mm"
include "mpbird.mm"
include "fmptd.mm"
include "wceq.mm"
include "w3a.mm"
include "df-3an.mm"
include "gaass.mm"
include "sylan2br.mm"
include "anassrs.mm"
include "mpteq2dva.mm"
include "simprl.mm"
include "simprr.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "mptexg.mm"
include "oveq1.mm"
include "mpteq2dv.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "ccom.mm"
include "wf.mm"
include "ffvelrnd.mm"
include "symgov.mm"
include "cxp.mm"
include "gaf.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "fovrnd.mm"
include "oveq2.mm"
include "cbvmptv.mm"
include "syl6eq.mm"
include "fmptco.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"
include "isghmd.mm"

theorem galactghm
  let vx: setvar x
  let vy: setvar y
  let c.po: class .(+)
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  let vw: setvar w
  let vz: setvar z
  assume galactghm.x: |- X = ( Base ` G )
  assume galactghm.h: |- H = ( SymGrp ` Y )
  assume galactghm.f: |- F = ( x e. X |-> ( y e. Y |-> ( x .(+) y ) ) )

  disjoint x y
  disjoint G x
  disjoint G y
  disjoint .(+) x
  disjoint .(+) y
  disjoint X x
  disjoint X y
  disjoint H x
  disjoint Y x
  disjoint Y y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint G w
  disjoint x z
  disjoint y z
  disjoint G z
  disjoint .(+) w
  disjoint .(+) z
  disjoint X w
  disjoint X z
  disjoint F w
  disjoint F z
  disjoint H w
  disjoint H z
  disjoint Y w
  disjoint Y z
  assert |- ( .(+) e. ( G GrpAct Y ) -> F e. ( G GrpHom H ) )

  proof
    c.po
    cG
    cY
    cga
    co
    wcel
    #
    vz
    vw
    cG
    cplusg
    cfv
    #
    cH
    cplusg
    cfv
    #
    cG
    cH
    cF
    cX
    cH
    cbs
    cfv
    #
    galactghm.x
    @3
    eqid
    #
    @1
    eqid
    #
    @2
    eqid
    #
    c.po
    cG
    cY
    gagrp
    #
    @0
    cY
    cvv
    wcel
    #
    cH
    cgrp
    wcel
    c.po
    cG
    cY
    gaset
    #
    cY
    cH
    cvv
    galactghm.h
    symggrp
    syl
    @0
    vx
    cX
    vy
    cY
    vx
    cv
    #
    vy
    cv
    #
    c.po
    co
    #
    cmpt
    #
    @3
    cF
    @0
    @10
    cX
    wcel
    #
    wa
    #
    @13
    @3
    wcel
    #
    cY
    cY
    @13
    wf1o
    #
    vy
    @10
    c.po
    @13
    cG
    cX
    cY
    galactghm.x
    @13
    eqid
    gapm
    @15
    @8
    @16
    @17
    wb
    @0
    @8
    @14
    @9
    adantr
    cY
    @3
    @13
    cH
    cvv
    galactghm.h
    @4
    elsymgbas
    syl
    mpbird
    galactghm.f
    fmptd
    #
    @0
    vz
    cv
    #
    cX
    wcel
    #
    vw
    cv
    #
    cX
    wcel
    #
    wa
    #
    wa
    #
    vy
    cY
    @19
    @21
    @1
    co
    #
    @11
    c.po
    co
    #
    cmpt
    #
    vy
    cY
    @19
    @21
    @11
    c.po
    co
    #
    c.po
    co
    #
    cmpt
    #
    @25
    cF
    cfv
    #
    @19
    cF
    cfv
    #
    @21
    cF
    cfv
    #
    @2
    co
    #
    @24
    vy
    cY
    @26
    @29
    @0
    @23
    @11
    cY
    wcel
    #
    @26
    @29
    wceq
    #
    @23
    @35
    wa
    @0
    @20
    @22
    @35
    w3a
    @36
    @20
    @22
    @35
    df-3an
    @19
    @21
    @11
    @1
    c.po
    cG
    cX
    cY
    galactghm.x
    @5
    gaass
    sylan2br
    anassrs
    mpteq2dva
    @24
    @25
    cX
    wcel
    #
    @27
    cvv
    wcel
    #
    @31
    @27
    wceq
    @24
    cG
    cgrp
    wcel
    #
    @20
    @22
    @37
    @0
    @39
    @23
    @7
    adantr
    @0
    @20
    @22
    simprl
    #
    @0
    @20
    @22
    simprr
    #
    cX
    @1
    cG
    @19
    @21
    galactghm.x
    @5
    grpcl
    syl3anc
    @24
    @8
    @38
    @0
    @8
    @23
    @9
    adantr
    #
    vy
    cY
    @26
    cvv
    mptexg
    syl
    vx
    @25
    @13
    @27
    cX
    cvv
    cF
    @10
    @25
    wceq
    vy
    cY
    @12
    @26
    @10
    @25
    @11
    c.po
    oveq1
    mpteq2dv
    galactghm.f
    fvmptg
    syl2anc
    @24
    @34
    @32
    @33
    ccom
    #
    @30
    @24
    @32
    @3
    wcel
    @33
    @3
    wcel
    @34
    @43
    wceq
    @24
    cX
    @3
    @19
    cF
    @0
    cX
    @3
    cF
    wf
    @23
    @18
    adantr
    #
    @40
    ffvelrnd
    @24
    cX
    @3
    @21
    cF
    @44
    @41
    ffvelrnd
    cY
    @3
    @2
    cH
    @32
    @33
    galactghm.h
    @4
    @6
    symgov
    syl2anc
    @24
    vy
    vx
    cY
    cY
    @28
    @19
    @10
    c.po
    co
    #
    @29
    @33
    @32
    @24
    @35
    wa
    @21
    @11
    cY
    cX
    cY
    c.po
    @0
    cX
    cY
    cxp
    cY
    c.po
    wf
    @23
    @35
    c.po
    cG
    cX
    cY
    galactghm.x
    gaf
    ad2antrr
    @24
    @22
    @35
    @41
    adantr
    @24
    @35
    simpr
    fovrnd
    @24
    @22
    vy
    cY
    @28
    cmpt
    #
    cvv
    wcel
    #
    @33
    @46
    wceq
    @41
    @24
    @8
    @47
    @42
    vy
    cY
    @28
    cvv
    mptexg
    syl
    vx
    @21
    @13
    @46
    cX
    cvv
    cF
    @10
    @21
    wceq
    vy
    cY
    @12
    @28
    @10
    @21
    @11
    c.po
    oveq1
    mpteq2dv
    galactghm.f
    fvmptg
    syl2anc
    @24
    @32
    vy
    cY
    @19
    @11
    c.po
    co
    #
    cmpt
    #
    vx
    cY
    @45
    cmpt
    @24
    @20
    @49
    cvv
    wcel
    #
    @32
    @49
    wceq
    @40
    @24
    @8
    @50
    @42
    vy
    cY
    @48
    cvv
    mptexg
    syl
    vx
    @19
    @13
    @49
    cX
    cvv
    cF
    @10
    @19
    wceq
    vy
    cY
    @12
    @48
    @10
    @19
    @11
    c.po
    oveq1
    mpteq2dv
    galactghm.f
    fvmptg
    syl2anc
    vy
    vx
    cY
    @48
    @45
    @11
    @10
    @19
    c.po
    oveq2
    cbvmptv
    syl6eq
    @10
    @28
    @19
    c.po
    oveq2
    fmptco
    eqtrd
    3eqtr4d
    isghmd
end
