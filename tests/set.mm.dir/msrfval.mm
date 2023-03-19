include "cmsr.mm"
include "cfv.mm"
include "cv.mm"
include "c1st.mm"
include "c2nd.mm"
include "csn.mm"
include "cun.mm"
include "cima.mm"
include "cuni.mm"
include "cxp.mm"
include "csb.mm"
include "cin.mm"
include "cotp.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cmpst.mm"
include "cmvrs.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "imaeq1d.mm"
include "unieqd.mm"
include "csbeq1d.mm"
include "ineq2d.mm"
include "oteq1d.mm"
include "csbeq2dv.mm"
include "mpteq12dv.mm"
include "df-msr.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "mpt0.mm"
include "eqcomi.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "mpteq1d.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem msrfval
  let vz: setvar z
  let cP: class P
  let cR: class R
  let cT: class T
  let vh: setvar h
  let cV: class V
  let vs: setvar s
  let va: setvar a
  let cA: class A
  let cD: class D
  let cH: class H
  let vt: setvar t
  let cZ: class Z
  assume msrfval.v: |- V = ( mVars ` T )
  assume msrfval.p: |- P = ( mPreSt ` T )
  assume msrfval.r: |- R = ( mStRed ` T )

  disjoint a h
  disjoint a s
  disjoint a z
  disjoint h s
  disjoint h z
  disjoint s z
  disjoint P a
  disjoint P h
  disjoint P s
  disjoint P z
  disjoint T a
  disjoint T h
  disjoint T s
  disjoint V z
  disjoint A a
  disjoint A h
  disjoint A s
  disjoint A z
  disjoint D a
  disjoint D h
  disjoint D s
  disjoint D z
  disjoint H a
  disjoint H h
  disjoint H s
  disjoint H z
  disjoint a t
  disjoint h t
  disjoint s t
  disjoint t z
  disjoint P t
  disjoint T t
  disjoint V t
  disjoint Z a
  disjoint Z h
  disjoint Z s
  disjoint Z z
  assert |- R = ( s e. P |-> [_ ( 2nd ` ( 1st ` s ) ) / h ]_ [_ ( 2nd ` s ) / a ]_ <. ( ( 1st ` ( 1st ` s ) ) i^i [_ U. ( V " ( h u. { a } ) ) / z ]_ ( z X. z ) ) , h , a >. )

  proof
    cR
    cT
    cmsr
    cfv
    #
    vs
    cP
    vh
    vs
    cv
    #
    c1st
    cfv
    #
    c2nd
    cfv
    #
    va
    @1
    c2nd
    cfv
    #
    @2
    c1st
    cfv
    #
    vz
    cV
    vh
    cv
    #
    va
    cv
    #
    csn
    cun
    #
    cima
    #
    cuni
    #
    vz
    cv
    #
    @11
    cxp
    #
    csb
    #
    cin
    #
    @6
    @7
    cotp
    #
    csb
    #
    csb
    #
    cmpt
    #
    msrfval.r
    cT
    cvv
    wcel
    #
    @0
    @18
    wceq
    vt
    cT
    vs
    vt
    cv
    #
    cmpst
    cfv
    #
    vh
    @3
    va
    @4
    @5
    vz
    @20
    cmvrs
    cfv
    #
    @8
    cima
    #
    cuni
    #
    @12
    csb
    #
    cin
    #
    @6
    @7
    cotp
    #
    csb
    #
    csb
    #
    cmpt
    @18
    cvv
    cmsr
    @20
    cT
    wceq
    #
    vs
    @21
    @29
    cP
    @17
    @30
    @21
    cT
    cmpst
    cfv
    #
    cP
    @20
    cT
    cmpst
    fveq2
    msrfval.p
    syl6eqr
    @30
    vh
    @3
    @28
    @16
    @30
    va
    @4
    @27
    @15
    @30
    @26
    @14
    @6
    @7
    @30
    @25
    @13
    @5
    @30
    vz
    @24
    @10
    @12
    @30
    @23
    @9
    @30
    @22
    cV
    @8
    @30
    @22
    cT
    cmvrs
    cfv
    cV
    @20
    cT
    cmvrs
    fveq2
    msrfval.v
    syl6eqr
    imaeq1d
    unieqd
    csbeq1d
    ineq2d
    oteq1d
    csbeq2dv
    csbeq2dv
    mpteq12dv
    vz
    vt
    vh
    vs
    va
    df-msr
    vs
    cP
    @17
    cP
    @31
    cvv
    msrfval.p
    cT
    cmpst
    fvex
    eqeltri
    mptex
    fvmpt
    @19
    wn
    #
    c0
    vs
    c0
    @17
    cmpt
    #
    @0
    @18
    @33
    c0
    vs
    @17
    mpt0
    eqcomi
    cT
    cmsr
    fvprc
    @32
    vs
    cP
    c0
    @17
    @32
    cP
    @31
    c0
    msrfval.p
    cT
    cmpst
    fvprc
    syl5eq
    mpteq1d
    3eqtr4a
    pm2.61i
    eqtri
end
