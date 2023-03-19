include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "cop.mm"
include "cvv.mm"
include "cmpt.mm"
include "co.mm"
include "c2nd.mm"
include "cmpt2.mm"
include "wceq.mm"
include "prfval.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "mpt2ex.mm"
include "op1std.mm"
include "syl.mm"
include "wa.mm"
include "simpr.mm"
include "fveq2d.mm"
include "opeq12d.mm"
include "wcel.mm"
include "opex.mm"
include "a1i.mm"
include "fvmptd.mm"

theorem prf1
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  let cK: class K
  let cY: class Y
  assume prfval.k: |- P = ( F pairF G )
  assume prfval.b: |- B = ( Base ` C )
  assume prfval.h: |- H = ( Hom ` C )
  assume prfval.c: |- ( ph -> F e. ( C Func D ) )
  assume prfval.d: |- ( ph -> G e. ( C Func E ) )
  assume prf1.x: |- ( ph -> X e. B )


  assert |- ( ph -> ( ( 1st ` P ) ` X ) = <. ( ( 1st ` F ) ` X ) , ( ( 1st ` G ) ` X ) >. )

  proof
    wph
    vx
    cX
    vx
    cv
    #
    cF
    c1st
    cfv
    #
    cfv
    #
    @0
    cG
    c1st
    cfv
    #
    cfv
    #
    cop
    #
    cX
    @1
    cfv
    #
    cX
    @3
    cfv
    #
    cop
    #
    cB
    cP
    c1st
    cfv
    #
    cvv
    wph
    cP
    vx
    cB
    @5
    cmpt
    #
    vx
    vy
    cB
    cB
    vh
    @0
    vy
    cv
    #
    cH
    co
    vh
    cv
    #
    @0
    @11
    cF
    c2nd
    cfv
    co
    cfv
    @12
    @0
    @11
    cG
    c2nd
    cfv
    co
    cfv
    cop
    cmpt
    #
    cmpt2
    #
    cop
    wceq
    @9
    @10
    wceq
    wph
    vx
    vy
    cB
    cC
    cD
    cP
    vh
    cE
    cF
    cG
    cH
    prfval.k
    prfval.b
    prfval.h
    prfval.c
    prfval.d
    prfval
    @10
    @14
    cP
    vx
    cB
    @5
    cB
    cC
    cbs
    cfv
    cvv
    prfval.b
    cC
    cbs
    fvex
    eqeltri
    #
    mptex
    vx
    vy
    cB
    cB
    @13
    @15
    @15
    mpt2ex
    op1std
    syl
    wph
    @0
    cX
    wceq
    #
    wa
    #
    @2
    @6
    @4
    @7
    @17
    @0
    cX
    @1
    wph
    @16
    simpr
    #
    fveq2d
    @17
    @0
    cX
    @3
    @18
    fveq2d
    opeq12d
    prf1.x
    @8
    cvv
    wcel
    wph
    @6
    @7
    opex
    a1i
    fvmptd
end
