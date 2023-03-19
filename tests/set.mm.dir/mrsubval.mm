include "wf.mm"
include "wss.mm"
include "wcel.mm"
include "w3a.mm"
include "cun.mm"
include "cv.mm"
include "cfv.mm"
include "cs1.mm"
include "cif.mm"
include "cmpt.mm"
include "ccom.mm"
include "cgsu.mm"
include "co.mm"
include "cvv.mm"
include "wceq.mm"
include "mrsubfval.mm"
include "3adant3.mm"
include "wa.mm"
include "simpr.mm"
include "coeq2d.mm"
include "oveq2d.mm"
include "simp3.mm"
include "ovexd.mm"
include "fvmptd.mm"

theorem mrsubval
  let vv: setvar v
  let cA: class A
  let cC: class C
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cV: class V
  let cX: class X
  let ve: setvar e
  let vf: setvar f
  let vt: setvar t
  assume mrsubffval.c: |- C = ( mCN ` T )
  assume mrsubffval.v: |- V = ( mVR ` T )
  assume mrsubffval.r: |- R = ( mREx ` T )
  assume mrsubffval.s: |- S = ( mRSubst ` T )
  assume mrsubffval.g: |- G = ( freeMnd ` ( C u. V ) )

  disjoint A v
  disjoint C v
  disjoint F v
  disjoint R v
  disjoint X v
  disjoint T v
  disjoint V v
  disjoint e f
  disjoint e v
  disjoint A e
  disjoint f v
  disjoint A f
  disjoint e t
  disjoint C e
  disjoint f t
  disjoint C f
  disjoint t v
  disjoint C t
  disjoint F e
  disjoint F f
  disjoint R e
  disjoint R f
  disjoint R t
  disjoint X e
  disjoint G e
  disjoint G f
  disjoint G t
  disjoint T e
  disjoint T f
  disjoint T t
  disjoint V e
  disjoint V f
  disjoint V t
  assert |- ( ( F : A --> R /\ A C_ V /\ X e. R ) -> ( ( S ` F ) ` X ) = ( G gsum ( ( v e. ( C u. V ) |-> if ( v e. A , ( F ` v ) , <" v "> ) ) o. X ) ) )

  proof
    cA
    cR
    cF
    wf
    #
    cA
    cV
    wss
    #
    cX
    cR
    wcel
    #
    w3a
    #
    ve
    cX
    cG
    vv
    cC
    cV
    cun
    vv
    cv
    #
    cA
    wcel
    @4
    cF
    cfv
    @4
    cs1
    cif
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
    cG
    @5
    cX
    ccom
    #
    cgsu
    co
    cR
    cF
    cS
    cfv
    #
    cvv
    @0
    @1
    @10
    ve
    cR
    @8
    cmpt
    wceq
    @2
    vv
    cA
    cC
    cR
    cS
    cT
    ve
    cF
    cG
    cV
    mrsubffval.c
    mrsubffval.v
    mrsubffval.r
    mrsubffval.s
    mrsubffval.g
    mrsubfval
    3adant3
    @3
    @6
    cX
    wceq
    #
    wa
    #
    @7
    @9
    cG
    cgsu
    @12
    @6
    cX
    @5
    @3
    @11
    simpr
    coeq2d
    oveq2d
    @0
    @1
    @2
    simp3
    @3
    cG
    @9
    cgsu
    ovexd
    fvmptd
end
