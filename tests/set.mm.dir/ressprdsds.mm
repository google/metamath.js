include "cxp.mm"
include "cres.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "ovres.mm"
include "adantl.mm"
include "cmpt.mm"
include "cprds.mm"
include "cds.mm"
include "cfv.mm"
include "cress.mm"
include "crn.mm"
include "cc0.mm"
include "csn.mm"
include "cun.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "eqid.mm"
include "ressds.mm"
include "syl.mm"
include "oveqd.mm"
include "mpteq2dva.mm"
include "adantr.mm"
include "rneqd.mm"
include "uneq1d.mm"
include "supeq1d.mm"
include "cbs.mm"
include "ralrimiva.mm"
include "wss.mm"
include "cixp.mm"
include "ressbasss.mm"
include "a1i.mm"
include "ss2ixp.mm"
include "cvv.mm"
include "ovex.mm"
include "rgenw.mm"
include "prdsbas3.mm"
include "3sstr4d.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "sseqtrd.mm"
include "simprl.mm"
include "sseldd.mm"
include "simprr.mm"
include "prdsdsval2.mm"
include "eleqtrd.mm"
include "3eqtr4d.mm"
include "oveqdr.mm"
include "eqtr2d.mm"
include "ralrimivva.mm"
include "wfn.mm"
include "wb.mm"
include "mptexg.mm"
include "cdm.mm"
include "dmmpti.mm"
include "prdsdsfn.mm"
include "sqxpeqd.mm"
include "fneq12d.mm"
include "mpbird.mm"
include "dmmptg.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "fnssres.mm"
include "eqfnov2.mm"

theorem ressprdsds
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cE: class E
  let cH: class H
  let cI: class I
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vf: setvar f
  let vg: setvar g
  assume ressprdsds.y: |- ( ph -> Y = ( S Xs_ ( x e. I |-> R ) ) )
  assume ressprdsds.h: |- ( ph -> H = ( T Xs_ ( x e. I |-> ( R |`s A ) ) ) )
  assume ressprdsds.b: |- B = ( Base ` H )
  assume ressprdsds.d: |- D = ( dist ` Y )
  assume ressprdsds.e: |- E = ( dist ` H )
  assume ressprdsds.s: |- ( ph -> S e. U )
  assume ressprdsds.t: |- ( ph -> T e. V )
  assume ressprdsds.i: |- ( ph -> I e. W )
  assume ressprdsds.r: |- ( ( ph /\ x e. I ) -> R e. X )
  assume ressprdsds.a: |- ( ( ph /\ x e. I ) -> A e. Z )

  disjoint I x
  disjoint ph x
  disjoint f g
  disjoint B f
  disjoint B g
  disjoint D f
  disjoint D g
  disjoint E f
  disjoint E g
  disjoint f x
  disjoint f ph
  disjoint g x
  disjoint g ph
  assert |- ( ph -> E = ( D |` ( B X. B ) ) )

  proof
    wph
    cE
    cD
    cB
    cB
    cxp
    #
    cres
    #
    wceq
    #
    vf
    cv
    #
    vg
    cv
    #
    cE
    co
    #
    @3
    @4
    @1
    co
    #
    wceq
    #
    vg
    cB
    wral
    vf
    cB
    wral
    #
    wph
    @7
    vf
    vg
    cB
    cB
    wph
    @3
    cB
    wcel
    #
    @4
    cB
    wcel
    #
    wa
    #
    wa
    #
    @6
    @3
    @4
    cD
    co
    #
    @5
    @11
    @6
    @13
    wceq
    wph
    @3
    @4
    cB
    cB
    cD
    ovres
    adantl
    @12
    @3
    @4
    cS
    vx
    cI
    cR
    cmpt
    #
    cprds
    co
    #
    cds
    cfv
    #
    co
    #
    @3
    @4
    cT
    vx
    cI
    cR
    cA
    cress
    co
    #
    cmpt
    #
    cprds
    co
    #
    cds
    cfv
    #
    co
    #
    @13
    @5
    @12
    vx
    cI
    vx
    cv
    #
    @3
    cfv
    #
    @23
    @4
    cfv
    #
    cR
    cds
    cfv
    #
    co
    #
    cmpt
    #
    crn
    #
    cc0
    csn
    #
    cun
    #
    cxr
    clt
    csup
    vx
    cI
    @24
    @25
    @18
    cds
    cfv
    #
    co
    #
    cmpt
    #
    crn
    #
    @30
    cun
    #
    cxr
    clt
    csup
    @17
    @22
    @12
    cxr
    @31
    @36
    clt
    @12
    @29
    @35
    @30
    @12
    @28
    @34
    wph
    @28
    @34
    wceq
    @11
    wph
    vx
    cI
    @27
    @33
    wph
    @23
    cI
    wcel
    wa
    #
    @26
    @32
    @24
    @25
    @37
    cA
    cZ
    wcel
    @26
    @32
    wceq
    ressprdsds.a
    cA
    @26
    cR
    @18
    cZ
    @18
    eqid
    #
    @26
    eqid
    #
    ressds
    syl
    oveqd
    mpteq2dva
    adantr
    rneqd
    uneq1d
    supeq1d
    @12
    vx
    @15
    cbs
    cfv
    #
    @16
    cR
    cS
    @26
    @3
    @4
    cI
    cU
    cW
    cX
    @15
    @15
    eqid
    #
    @40
    eqid
    #
    wph
    cS
    cU
    wcel
    @11
    ressprdsds.s
    adantr
    wph
    cI
    cW
    wcel
    #
    @11
    ressprdsds.i
    adantr
    #
    wph
    cR
    cX
    wcel
    #
    vx
    cI
    wral
    #
    @11
    wph
    @45
    vx
    cI
    ressprdsds.r
    ralrimiva
    #
    adantr
    @12
    cB
    @40
    @3
    @12
    cB
    cY
    cbs
    cfv
    #
    @40
    wph
    cB
    @48
    wss
    #
    @11
    wph
    @20
    cbs
    cfv
    #
    @40
    cB
    @48
    wph
    vx
    cI
    @18
    cbs
    cfv
    #
    cixp
    #
    vx
    cI
    cR
    cbs
    cfv
    #
    cixp
    #
    @50
    @40
    wph
    @51
    @53
    wss
    #
    vx
    cI
    wral
    @52
    @54
    wss
    wph
    @55
    vx
    cI
    @55
    @37
    cA
    @53
    @18
    cR
    @38
    @53
    eqid
    #
    ressbasss
    a1i
    ralrimiva
    vx
    cI
    @51
    @53
    ss2ixp
    syl
    wph
    vx
    @50
    @18
    cT
    cI
    @51
    cV
    cW
    cvv
    @20
    @20
    eqid
    #
    @50
    eqid
    #
    ressprdsds.t
    ressprdsds.i
    @18
    cvv
    wcel
    #
    vx
    cI
    wral
    #
    wph
    @59
    vx
    cI
    cR
    cA
    cress
    ovex
    #
    rgenw
    #
    a1i
    @51
    eqid
    prdsbas3
    wph
    vx
    @40
    cR
    cS
    cI
    @53
    cU
    cW
    cX
    @15
    @41
    @42
    ressprdsds.s
    ressprdsds.i
    @47
    @56
    prdsbas3
    3sstr4d
    wph
    cB
    cH
    cbs
    cfv
    @50
    ressprdsds.b
    wph
    cH
    @20
    cbs
    ressprdsds.h
    fveq2d
    syl5eq
    #
    wph
    cY
    @15
    cbs
    ressprdsds.y
    fveq2d
    #
    3sstr4d
    #
    adantr
    wph
    @48
    @40
    wceq
    @11
    @64
    adantr
    sseqtrd
    #
    wph
    @9
    @10
    simprl
    #
    sseldd
    @12
    cB
    @40
    @4
    @66
    wph
    @9
    @10
    simprr
    #
    sseldd
    @39
    @16
    eqid
    #
    prdsdsval2
    @12
    vx
    @50
    @21
    @18
    cT
    @32
    @3
    @4
    cI
    cV
    cW
    cvv
    @20
    @57
    @58
    wph
    cT
    cV
    wcel
    @11
    ressprdsds.t
    adantr
    @44
    @60
    @12
    @62
    a1i
    @12
    @3
    cB
    @50
    @67
    wph
    cB
    @50
    wceq
    @11
    @63
    adantr
    #
    eleqtrd
    @12
    @4
    cB
    @50
    @68
    @70
    eleqtrd
    @32
    eqid
    @21
    eqid
    #
    prdsdsval2
    3eqtr4d
    wph
    @11
    vf
    vg
    cD
    @16
    wph
    cD
    cY
    cds
    cfv
    @16
    ressprdsds.d
    wph
    cY
    @15
    cds
    ressprdsds.y
    fveq2d
    syl5eq
    #
    oveqdr
    wph
    @11
    vf
    vg
    cE
    @21
    wph
    cE
    cH
    cds
    cfv
    @21
    ressprdsds.e
    wph
    cH
    @20
    cds
    ressprdsds.h
    fveq2d
    syl5eq
    #
    oveqdr
    3eqtr4d
    eqtr2d
    ralrimivva
    wph
    cE
    @0
    wfn
    #
    @1
    @0
    wfn
    #
    @2
    @8
    wb
    wph
    @74
    @21
    @50
    @50
    cxp
    #
    wfn
    wph
    @50
    @21
    @20
    @19
    cT
    cI
    cV
    cvv
    @57
    ressprdsds.t
    wph
    @43
    @19
    cvv
    wcel
    ressprdsds.i
    vx
    cI
    @18
    cW
    mptexg
    syl
    @58
    @19
    cdm
    cI
    wceq
    wph
    vx
    cI
    @18
    @19
    @61
    @19
    eqid
    dmmpti
    a1i
    @71
    prdsdsfn
    wph
    @0
    @76
    cE
    @21
    @73
    wph
    cB
    @50
    @63
    sqxpeqd
    fneq12d
    mpbird
    wph
    cD
    @48
    @48
    cxp
    #
    wfn
    #
    @0
    @77
    wss
    #
    @75
    wph
    @78
    @16
    @40
    @40
    cxp
    #
    wfn
    wph
    @40
    @16
    @15
    @14
    cS
    cI
    cU
    cvv
    @41
    ressprdsds.s
    wph
    @43
    @14
    cvv
    wcel
    ressprdsds.i
    vx
    cI
    cR
    cW
    mptexg
    syl
    @42
    wph
    @46
    @14
    cdm
    cI
    wceq
    @47
    vx
    cI
    cR
    cX
    dmmptg
    syl
    @69
    prdsdsfn
    wph
    @77
    @80
    cD
    @16
    @72
    wph
    @48
    @40
    @64
    sqxpeqd
    fneq12d
    mpbird
    wph
    @49
    @49
    @79
    @65
    @65
    cB
    @48
    cB
    @48
    xpss12
    syl2anc
    @77
    @0
    cD
    fnssres
    syl2anc
    vf
    vg
    cB
    cB
    cE
    @1
    eqfnov2
    syl2anc
    mpbird
end
