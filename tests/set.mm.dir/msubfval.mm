include "cvv.mm"
include "wcel.mm"
include "wf.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "cmpt.mm"
include "wceq.mm"
include "wi.mm"
include "cpm.mm"
include "co.mm"
include "msubffval.mm"
include "adantr.mm"
include "simplr.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "opeq2d.mm"
include "mpteq2dva.mm"
include "cmrex.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cmvar.mm"
include "pm3.2i.mm"
include "a1i.mm"
include "elpm2r.mm"
include "sylan.mm"
include "cmex.mm"
include "mptex.mm"
include "fvmptd.mm"
include "ex.mm"
include "wn.mm"
include "c0.mm"
include "0fv.mm"
include "mpt0.mm"
include "eqtr4i.mm"
include "cmsub.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "mpteq1d.mm"
include "3eqtr4a.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem msubfval
  let cA: class A
  let cR: class R
  let cS: class S
  let cT: class T
  let ve: setvar e
  let cE: class E
  let cF: class F
  let cO: class O
  let cV: class V
  let vf: setvar f
  let vt: setvar t
  let cX: class X
  assume msubffval.v: |- V = ( mVR ` T )
  assume msubffval.r: |- R = ( mREx ` T )
  assume msubffval.s: |- S = ( mSubst ` T )
  assume msubffval.e: |- E = ( mEx ` T )
  assume msubffval.o: |- O = ( mRSubst ` T )

  disjoint E e
  disjoint O e
  disjoint R e
  disjoint T e
  disjoint V e
  disjoint A e
  disjoint F e
  disjoint e f
  disjoint e t
  disjoint f t
  disjoint E f
  disjoint E t
  disjoint O f
  disjoint O t
  disjoint R f
  disjoint R t
  disjoint T f
  disjoint T t
  disjoint V f
  disjoint V t
  disjoint A f
  disjoint F f
  disjoint X e
  assert |- ( ( F : A --> R /\ A C_ V ) -> ( S ` F ) = ( e e. E |-> <. ( 1st ` e ) , ( ( O ` F ) ` ( 2nd ` e ) ) >. ) )

  proof
    cT
    cvv
    wcel
    #
    cA
    cR
    cF
    wf
    cA
    cV
    wss
    wa
    #
    cF
    cS
    cfv
    #
    ve
    cE
    ve
    cv
    #
    c1st
    cfv
    #
    @3
    c2nd
    cfv
    #
    cF
    cO
    cfv
    #
    cfv
    #
    cop
    #
    cmpt
    #
    wceq
    #
    wi
    @0
    @1
    @10
    @0
    @1
    wa
    #
    vf
    cF
    ve
    cE
    @4
    @5
    vf
    cv
    #
    cO
    cfv
    #
    cfv
    #
    cop
    #
    cmpt
    #
    @9
    cR
    cV
    cpm
    co
    #
    cS
    cvv
    @0
    cS
    vf
    @17
    @16
    cmpt
    wceq
    @1
    cR
    cS
    cT
    ve
    vf
    cE
    cO
    cV
    cvv
    msubffval.v
    msubffval.r
    msubffval.s
    msubffval.e
    msubffval.o
    msubffval
    adantr
    @11
    @12
    cF
    wceq
    #
    wa
    #
    ve
    cE
    @15
    @8
    @19
    @3
    cE
    wcel
    #
    wa
    #
    @14
    @7
    @4
    @21
    @5
    @13
    @6
    @21
    @12
    cF
    cO
    @11
    @18
    @20
    simplr
    fveq2d
    fveq1d
    opeq2d
    mpteq2dva
    @0
    cR
    cvv
    wcel
    #
    cV
    cvv
    wcel
    #
    wa
    #
    @1
    cF
    @17
    wcel
    @24
    @0
    @22
    @23
    cR
    cT
    cmrex
    cfv
    cvv
    msubffval.r
    cT
    cmrex
    fvex
    eqeltri
    cV
    cT
    cmvar
    cfv
    cvv
    msubffval.v
    cT
    cmvar
    fvex
    eqeltri
    pm3.2i
    a1i
    cR
    cV
    cA
    cF
    cvv
    cvv
    elpm2r
    sylan
    @9
    cvv
    wcel
    @11
    ve
    cE
    @8
    cE
    cT
    cmex
    cfv
    #
    cvv
    msubffval.e
    cT
    cmex
    fvex
    eqeltri
    mptex
    a1i
    fvmptd
    ex
    @0
    wn
    #
    @10
    @1
    @26
    cF
    c0
    cfv
    #
    ve
    c0
    @8
    cmpt
    #
    @2
    @9
    @27
    c0
    @28
    cF
    0fv
    ve
    @8
    mpt0
    eqtr4i
    @26
    cF
    cS
    c0
    @26
    cS
    cT
    cmsub
    cfv
    c0
    msubffval.s
    cT
    cmsub
    fvprc
    syl5eq
    fveq1d
    @26
    ve
    cE
    c0
    @8
    @26
    cE
    @25
    c0
    msubffval.e
    cT
    cmex
    fvprc
    syl5eq
    mpteq1d
    3eqtr4a
    a1d
    pm2.61i
end
