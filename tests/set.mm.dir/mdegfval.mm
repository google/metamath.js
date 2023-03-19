include "cmdg.mm"
include "co.mm"
include "cv.mm"
include "csupp.mm"
include "cima.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "ccnfld.mm"
include "cgsu.mm"
include "crn.mm"
include "cmpl.mm"
include "cbs.mm"
include "cfv.mm"
include "c0g.mm"
include "oveq12.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "mpteq1d.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "adantl.mm"
include "mpteq12dv.mm"
include "df-mdeg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "ovmpt2a.mm"
include "cres.mm"
include "reseq1i.mm"
include "cdm.mm"
include "suppssdm.mm"
include "wf.mm"
include "eqid.mm"
include "simpr.mm"
include "mplelf.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "resmptd.mm"
include "syl5req.mm"
include "df-ima.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "wn.mm"
include "c0.mm"
include "reldmmdeg.mm"
include "ovprc.mm"
include "mpt0.mm"
include "reldmmpl.mm"
include "syl5eq.mm"
include "base0.mm"
include "3eqtr4g.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem mdegfval
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let vf: setvar f
  let vh: setvar h
  let vm: setvar m
  let cH: class H
  let cI: class I
  let c.0: class .0.
  let vi: setvar i
  let vr: setvar r
  assume mdegval.d: |- D = ( I mDeg R )
  assume mdegval.p: |- P = ( I mPoly R )
  assume mdegval.b: |- B = ( Base ` P )
  assume mdegval.z: |- .0. = ( 0g ` R )
  assume mdegval.a: |- A = { m e. ( NN0 ^m I ) | ( `' m " NN ) e. Fin }
  assume mdegval.h: |- H = ( h e. A |-> ( CCfld gsum h ) )

  disjoint A h
  disjoint B f
  disjoint I f
  disjoint I m
  disjoint R f
  disjoint .0. h
  disjoint f h
  disjoint B i
  disjoint B r
  disjoint f i
  disjoint f r
  disjoint i r
  disjoint I i
  disjoint I r
  disjoint R i
  disjoint R r
  disjoint .0. i
  disjoint .0. r
  disjoint h i
  disjoint h r
  assert |- D = ( f e. B |-> sup ( ( H " ( f supp .0. ) ) , RR* , < ) )

  proof
    cD
    cI
    cR
    cmdg
    co
    #
    vf
    cB
    cH
    vf
    cv
    #
    c.0
    csupp
    co
    #
    cima
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    mdegval.d
    cI
    cvv
    wcel
    cR
    cvv
    wcel
    wa
    #
    @0
    @5
    wceq
    @6
    @0
    vf
    cB
    vh
    @2
    ccnfld
    vh
    cv
    cgsu
    co
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    @5
    vi
    vr
    cI
    cR
    cvv
    cvv
    vf
    vi
    cv
    #
    vr
    cv
    #
    cmpl
    co
    #
    cbs
    cfv
    #
    vh
    @1
    @13
    c0g
    cfv
    #
    csupp
    co
    #
    @7
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cmpt
    @11
    cmdg
    @12
    cI
    wceq
    #
    @13
    cR
    wceq
    #
    wa
    #
    vf
    @15
    @20
    cB
    @10
    @23
    @15
    cP
    cbs
    cfv
    #
    cB
    @23
    @14
    cP
    cbs
    @23
    @14
    cI
    cR
    cmpl
    co
    #
    cP
    @12
    cI
    @13
    cR
    cmpl
    oveq12
    mdegval.p
    syl6eqr
    fveq2d
    mdegval.b
    syl6eqr
    @22
    @20
    @10
    wceq
    @21
    @22
    cxr
    @19
    @9
    clt
    @22
    @18
    @8
    @22
    vh
    @17
    @2
    @7
    @22
    @16
    c.0
    @1
    csupp
    @22
    @16
    cR
    c0g
    cfv
    c.0
    @13
    cR
    c0g
    fveq2
    mdegval.z
    syl6eqr
    oveq2d
    mpteq1d
    rneqd
    supeq1d
    adantl
    mpteq12dv
    vf
    vh
    vi
    vr
    df-mdeg
    vf
    cB
    @10
    cB
    @24
    cvv
    mdegval.b
    cP
    cbs
    fvex
    eqeltri
    mptex
    ovmpt2a
    @6
    vf
    cB
    @10
    @4
    @6
    @1
    cB
    wcel
    #
    wa
    #
    cxr
    @9
    @3
    clt
    @27
    @9
    cH
    @2
    cres
    #
    crn
    @3
    @27
    @8
    @28
    @27
    @28
    vh
    cA
    @7
    cmpt
    #
    @2
    cres
    @8
    cH
    @29
    @2
    mdegval.h
    reseq1i
    @27
    vh
    cA
    @2
    @7
    @27
    @1
    cdm
    #
    @2
    cA
    @1
    c.0
    suppssdm
    @27
    cA
    cR
    cbs
    cfv
    #
    @1
    wf
    @30
    cA
    wceq
    @27
    cB
    cA
    cP
    cR
    vm
    cI
    @31
    @1
    mdegval.p
    @31
    eqid
    mdegval.b
    mdegval.a
    @6
    @26
    simpr
    mplelf
    cA
    @31
    @1
    fdm
    syl
    syl5sseq
    resmptd
    syl5req
    rneqd
    cH
    @2
    df-ima
    syl6eqr
    supeq1d
    mpteq2dva
    eqtrd
    @6
    wn
    #
    @0
    vf
    c0
    @4
    cmpt
    #
    @5
    @32
    @0
    c0
    @33
    cI
    cR
    cmdg
    reldmmdeg
    ovprc
    vf
    @4
    mpt0
    syl6eqr
    @32
    vf
    cB
    c0
    @4
    @32
    @24
    c0
    cbs
    cfv
    cB
    c0
    @32
    cP
    c0
    cbs
    @32
    cP
    @25
    c0
    mdegval.p
    cI
    cR
    cmpl
    reldmmpl
    ovprc
    syl5eq
    fveq2d
    mdegval.b
    base0
    3eqtr4g
    mpteq1d
    eqtr4d
    pm2.61i
    eqtri
end
