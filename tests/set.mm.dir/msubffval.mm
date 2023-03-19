include "wcel.mm"
include "cvv.mm"
include "cpm.mm"
include "co.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "cmpt.mm"
include "wceq.mm"
include "elex.mm"
include "cmsub.mm"
include "cmrex.mm"
include "cmvar.mm"
include "cmex.mm"
include "cmrsub.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveq12d.mm"
include "fveq1d.mm"
include "opeq2d.mm"
include "mpteq12dv.mm"
include "df-msub.mm"
include "ovex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem msubffval
  let cR: class R
  let cS: class S
  let cT: class T
  let ve: setvar e
  let vf: setvar f
  let cE: class E
  let cO: class O
  let cV: class V
  let cW: class W
  let vt: setvar t
  let cA: class A
  let cF: class F
  let cX: class X
  assume msubffval.v: |- V = ( mVR ` T )
  assume msubffval.r: |- R = ( mREx ` T )
  assume msubffval.s: |- S = ( mSubst ` T )
  assume msubffval.e: |- E = ( mEx ` T )
  assume msubffval.o: |- O = ( mRSubst ` T )

  disjoint e f
  disjoint E e
  disjoint E f
  disjoint O e
  disjoint O f
  disjoint R e
  disjoint R f
  disjoint T e
  disjoint T f
  disjoint V e
  disjoint V f
  disjoint e t
  disjoint f t
  disjoint E t
  disjoint O t
  disjoint R t
  disjoint T t
  disjoint V t
  disjoint A e
  disjoint A f
  disjoint F e
  disjoint F f
  disjoint X e
  assert |- ( T e. W -> S = ( f e. ( R ^pm V ) |-> ( e e. E |-> <. ( 1st ` e ) , ( ( O ` f ) ` ( 2nd ` e ) ) >. ) ) )

  proof
    cT
    cW
    wcel
    cT
    cvv
    wcel
    #
    cS
    vf
    cR
    cV
    cpm
    co
    #
    ve
    cE
    ve
    cv
    #
    c1st
    cfv
    #
    @2
    c2nd
    cfv
    #
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
    cmpt
    #
    wceq
    cT
    cW
    elex
    @0
    cS
    cT
    cmsub
    cfv
    @10
    msubffval.s
    vt
    cT
    vf
    vt
    cv
    #
    cmrex
    cfv
    #
    @11
    cmvar
    cfv
    #
    cpm
    co
    #
    ve
    @11
    cmex
    cfv
    #
    @3
    @4
    @5
    @11
    cmrsub
    cfv
    #
    cfv
    #
    cfv
    #
    cop
    #
    cmpt
    #
    cmpt
    @10
    cvv
    cmsub
    @11
    cT
    wceq
    #
    vf
    @14
    @20
    @1
    @9
    @21
    @12
    cR
    @13
    cV
    cpm
    @21
    @12
    cT
    cmrex
    cfv
    cR
    @11
    cT
    cmrex
    fveq2
    msubffval.r
    syl6eqr
    @21
    @13
    cT
    cmvar
    cfv
    cV
    @11
    cT
    cmvar
    fveq2
    msubffval.v
    syl6eqr
    oveq12d
    @21
    ve
    @15
    @19
    cE
    @8
    @21
    @15
    cT
    cmex
    cfv
    cE
    @11
    cT
    cmex
    fveq2
    msubffval.e
    syl6eqr
    @21
    @18
    @7
    @3
    @21
    @4
    @17
    @6
    @21
    @5
    @16
    cO
    @21
    @16
    cT
    cmrsub
    cfv
    cO
    @11
    cT
    cmrsub
    fveq2
    msubffval.o
    syl6eqr
    fveq1d
    fveq1d
    opeq2d
    mpteq12dv
    mpteq12dv
    vt
    ve
    vf
    df-msub
    vf
    @1
    @9
    cR
    cV
    cpm
    ovex
    mptex
    fvmpt
    syl5eq
    syl
end
