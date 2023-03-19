include "wf.mm"
include "wss.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "msubfval.mm"
include "3adant3.mm"
include "wa.mm"
include "simpr.mm"
include "fveq2d.mm"
include "opeq12d.mm"
include "simp3.mm"
include "opex.mm"
include "a1i.mm"
include "fvmptd.mm"

theorem msubval
  let cA: class A
  let cR: class R
  let cS: class S
  let cT: class T
  let cE: class E
  let cF: class F
  let cO: class O
  let cV: class V
  let cX: class X
  let ve: setvar e
  let vf: setvar f
  let vt: setvar t
  assume msubffval.v: |- V = ( mVR ` T )
  assume msubffval.r: |- R = ( mREx ` T )
  assume msubffval.s: |- S = ( mSubst ` T )
  assume msubffval.e: |- E = ( mEx ` T )
  assume msubffval.o: |- O = ( mRSubst ` T )


  assert |- ( ( F : A --> R /\ A C_ V /\ X e. E ) -> ( ( S ` F ) ` X ) = <. ( 1st ` X ) , ( ( O ` F ) ` ( 2nd ` X ) ) >. )

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
    cE
    wcel
    #
    w3a
    #
    ve
    cX
    ve
    cv
    #
    c1st
    cfv
    #
    @4
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
    cX
    c1st
    cfv
    #
    cX
    c2nd
    cfv
    #
    @7
    cfv
    #
    cop
    #
    cE
    cF
    cS
    cfv
    #
    cvv
    @0
    @1
    @14
    ve
    cE
    @9
    cmpt
    wceq
    @2
    cA
    cR
    cS
    cT
    ve
    cE
    cF
    cO
    cV
    msubffval.v
    msubffval.r
    msubffval.s
    msubffval.e
    msubffval.o
    msubfval
    3adant3
    @3
    @4
    cX
    wceq
    #
    wa
    #
    @5
    @10
    @8
    @12
    @16
    @4
    cX
    c1st
    @3
    @15
    simpr
    #
    fveq2d
    @16
    @6
    @11
    @7
    @16
    @4
    cX
    c2nd
    @17
    fveq2d
    fveq2d
    opeq12d
    @0
    @1
    @2
    simp3
    @13
    cvv
    wcel
    @3
    @10
    @12
    opex
    a1i
    fvmptd
end
