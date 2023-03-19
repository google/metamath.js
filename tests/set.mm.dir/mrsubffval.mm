include "wcel.mm"
include "cmrsub.mm"
include "cfv.mm"
include "cpm.mm"
include "co.mm"
include "cun.mm"
include "cv.mm"
include "cdm.mm"
include "cs1.mm"
include "cif.mm"
include "cmpt.mm"
include "ccom.mm"
include "cgsu.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "cmrex.mm"
include "cmvar.mm"
include "cmcn.mm"
include "cfrmd.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveq12d.mm"
include "uneq12d.mm"
include "fveq2d.mm"
include "mpteq1d.mm"
include "coeq1d.mm"
include "mpteq12dv.mm"
include "df-mrsub.mm"
include "ovex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"
include "syl5eq.mm"

theorem mrsubffval
  let vv: setvar v
  let cC: class C
  let cR: class R
  let cS: class S
  let cT: class T
  let ve: setvar e
  let vf: setvar f
  let cG: class G
  let cV: class V
  let cW: class W
  let cA: class A
  let vt: setvar t
  let cF: class F
  let cX: class X
  assume mrsubffval.c: |- C = ( mCN ` T )
  assume mrsubffval.v: |- V = ( mVR ` T )
  assume mrsubffval.r: |- R = ( mREx ` T )
  assume mrsubffval.s: |- S = ( mRSubst ` T )
  assume mrsubffval.g: |- G = ( freeMnd ` ( C u. V ) )

  disjoint e f
  disjoint e v
  disjoint f v
  disjoint C e
  disjoint C f
  disjoint C v
  disjoint R e
  disjoint R f
  disjoint R v
  disjoint G e
  disjoint G f
  disjoint T e
  disjoint T f
  disjoint T v
  disjoint V e
  disjoint V f
  disjoint V v
  disjoint A e
  disjoint A f
  disjoint A v
  disjoint e t
  disjoint f t
  disjoint t v
  disjoint C t
  disjoint F e
  disjoint F f
  disjoint F v
  disjoint R t
  disjoint X e
  disjoint X v
  disjoint G t
  disjoint T t
  disjoint V t
  assert |- ( T e. W -> S = ( f e. ( R ^pm V ) |-> ( e e. R |-> ( G gsum ( ( v e. ( C u. V ) |-> if ( v e. dom f , ( f ` v ) , <" v "> ) ) o. e ) ) ) ) )

  proof
    cT
    cW
    wcel
    #
    cS
    cT
    cmrsub
    cfv
    #
    vf
    cR
    cV
    cpm
    co
    #
    ve
    cR
    cG
    vv
    cC
    cV
    cun
    #
    vv
    cv
    #
    vf
    cv
    #
    cdm
    wcel
    @4
    @5
    cfv
    @4
    cs1
    cif
    #
    cmpt
    #
    ve
    cv
    #
    ccom
    #
    cgsu
    co
    #
    cmpt
    #
    cmpt
    #
    mrsubffval.s
    @0
    cT
    cvv
    wcel
    @1
    @12
    wceq
    cT
    cW
    elex
    vt
    cT
    vf
    vt
    cv
    #
    cmrex
    cfv
    #
    @13
    cmvar
    cfv
    #
    cpm
    co
    #
    ve
    @14
    @13
    cmcn
    cfv
    #
    @15
    cun
    #
    cfrmd
    cfv
    #
    vv
    @18
    @6
    cmpt
    #
    @8
    ccom
    #
    cgsu
    co
    #
    cmpt
    #
    cmpt
    @12
    cvv
    cmrsub
    @13
    cT
    wceq
    #
    vf
    @16
    @23
    @2
    @11
    @24
    @14
    cR
    @15
    cV
    cpm
    @24
    @14
    cT
    cmrex
    cfv
    cR
    @13
    cT
    cmrex
    fveq2
    mrsubffval.r
    syl6eqr
    #
    @24
    @15
    cT
    cmvar
    cfv
    cV
    @13
    cT
    cmvar
    fveq2
    mrsubffval.v
    syl6eqr
    #
    oveq12d
    @24
    ve
    @14
    @22
    cR
    @10
    @25
    @24
    @19
    cG
    @21
    @9
    cgsu
    @24
    @19
    @3
    cfrmd
    cfv
    cG
    @24
    @18
    @3
    cfrmd
    @24
    @17
    cC
    @15
    cV
    @24
    @17
    cT
    cmcn
    cfv
    cC
    @13
    cT
    cmcn
    fveq2
    mrsubffval.c
    syl6eqr
    @26
    uneq12d
    #
    fveq2d
    mrsubffval.g
    syl6eqr
    @24
    @20
    @7
    @8
    @24
    vv
    @18
    @3
    @6
    @27
    mpteq1d
    coeq1d
    oveq12d
    mpteq12dv
    mpteq12dv
    vv
    vt
    ve
    vf
    df-mrsub
    vf
    @2
    @11
    cR
    cV
    cpm
    ovex
    mptex
    fvmpt
    syl
    syl5eq
end
