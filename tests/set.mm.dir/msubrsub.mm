include "wf.mm"
include "wss.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "wceq.mm"
include "msubval.mm"
include "fvex.mm"
include "op2ndd.mm"
include "syl.mm"

theorem msubrsub
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


  assert |- ( ( F : A --> R /\ A C_ V /\ X e. E ) -> ( 2nd ` ( ( S ` F ) ` X ) ) = ( ( O ` F ) ` ( 2nd ` X ) ) )

  proof
    cA
    cR
    cF
    wf
    cA
    cV
    wss
    cX
    cE
    wcel
    w3a
    cX
    cF
    cS
    cfv
    cfv
    #
    cX
    c1st
    cfv
    #
    cX
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
    wceq
    @0
    c2nd
    cfv
    @4
    wceq
    cA
    cR
    cS
    cT
    cE
    cF
    cO
    cV
    cX
    msubffval.v
    msubffval.r
    msubffval.s
    msubffval.e
    msubffval.o
    msubval
    @1
    @4
    @0
    cX
    c1st
    fvex
    @2
    @3
    fvex
    op2ndd
    syl
end
