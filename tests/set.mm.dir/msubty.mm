include "wf.mm"
include "wss.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "c1st.mm"
include "c2nd.mm"
include "cmrsub.mm"
include "cop.mm"
include "wceq.mm"
include "eqid.mm"
include "msubval.mm"
include "fvex.mm"
include "op1std.mm"
include "syl.mm"

theorem msubty
  let cA: class A
  let cR: class R
  let cS: class S
  let cT: class T
  let cE: class E
  let cF: class F
  let cV: class V
  let cX: class X
  let ve: setvar e
  let vf: setvar f
  let vt: setvar t
  let cO: class O
  assume msubffval.v: |- V = ( mVR ` T )
  assume msubffval.r: |- R = ( mREx ` T )
  assume msubffval.s: |- S = ( mSubst ` T )
  assume msubffval.e: |- E = ( mEx ` T )


  assert |- ( ( F : A --> R /\ A C_ V /\ X e. E ) -> ( 1st ` ( ( S ` F ) ` X ) ) = ( 1st ` X ) )

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
    cT
    cmrsub
    cfv
    #
    cfv
    #
    cfv
    #
    cop
    wceq
    @0
    c1st
    cfv
    @1
    wceq
    cA
    cR
    cS
    cT
    cE
    cF
    @3
    cV
    cX
    msubffval.v
    msubffval.r
    msubffval.s
    msubffval.e
    @3
    eqid
    msubval
    @1
    @5
    @0
    cX
    c1st
    fvex
    @2
    @4
    fvex
    op1std
    syl
end
