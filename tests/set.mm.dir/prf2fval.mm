include "cv.mm"
include "co.mm"
include "c2nd.mm"
include "cfv.mm"
include "cop.mm"
include "cmpt.mm"
include "cvv.mm"
include "c1st.mm"
include "cmpt2.mm"
include "wceq.mm"
include "prfval.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "mpt2ex.mm"
include "op2ndd.mm"
include "syl.mm"
include "wa.mm"
include "simprl.mm"
include "simprr.mm"
include "oveq12d.mm"
include "fveq1d.mm"
include "opeq12d.mm"
include "mpteq12dv.mm"
include "wcel.mm"
include "ovex.mm"
include "a1i.mm"
include "ovmpt2d.mm"

theorem prf2fval
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let vh: setvar h
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cK: class K
  assume prfval.k: |- P = ( F pairF G )
  assume prfval.b: |- B = ( Base ` C )
  assume prfval.h: |- H = ( Hom ` C )
  assume prfval.c: |- ( ph -> F e. ( C Func D ) )
  assume prfval.d: |- ( ph -> G e. ( C Func E ) )
  assume prf1.x: |- ( ph -> X e. B )
  assume prf2.y: |- ( ph -> Y e. B )

  disjoint B h
  disjoint F h
  disjoint h ph
  disjoint G h
  disjoint X h
  disjoint Y h
  disjoint H h
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint f g
  disjoint f h
  disjoint f x
  disjoint f y
  disjoint B f
  disjoint g h
  disjoint g x
  disjoint g y
  disjoint B g
  disjoint h x
  disjoint h y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint F b
  disjoint F f
  disjoint F g
  disjoint F x
  disjoint F y
  disjoint b ph
  disjoint f ph
  disjoint g ph
  disjoint ph x
  disjoint ph y
  disjoint D x
  disjoint D y
  disjoint G b
  disjoint G f
  disjoint G g
  disjoint G x
  disjoint G y
  disjoint K h
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint H b
  disjoint H f
  disjoint H g
  disjoint H x
  disjoint H y
  assert |- ( ph -> ( X ( 2nd ` P ) Y ) = ( h e. ( X H Y ) |-> <. ( ( X ( 2nd ` F ) Y ) ` h ) , ( ( X ( 2nd ` G ) Y ) ` h ) >. ) )

  proof
    wph
    vx
    vy
    cX
    cY
    cB
    cB
    vh
    vx
    cv
    #
    vy
    cv
    #
    cH
    co
    #
    vh
    cv
    #
    @0
    @1
    cF
    c2nd
    cfv
    #
    co
    #
    cfv
    #
    @3
    @0
    @1
    cG
    c2nd
    cfv
    #
    co
    #
    cfv
    #
    cop
    #
    cmpt
    #
    vh
    cX
    cY
    cH
    co
    #
    @3
    cX
    cY
    @4
    co
    #
    cfv
    #
    @3
    cX
    cY
    @7
    co
    #
    cfv
    #
    cop
    #
    cmpt
    #
    cP
    c2nd
    cfv
    #
    cvv
    wph
    cP
    vx
    cB
    @0
    cF
    c1st
    cfv
    cfv
    @0
    cG
    c1st
    cfv
    cfv
    cop
    #
    cmpt
    #
    vx
    vy
    cB
    cB
    @11
    cmpt2
    #
    cop
    wceq
    @19
    @22
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
    @21
    @22
    cP
    vx
    cB
    @20
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
    @11
    @23
    @23
    mpt2ex
    op2ndd
    syl
    wph
    @0
    cX
    wceq
    #
    @1
    cY
    wceq
    #
    wa
    wa
    #
    vh
    @2
    @10
    @12
    @17
    @26
    @0
    cX
    @1
    cY
    cH
    wph
    @24
    @25
    simprl
    #
    wph
    @24
    @25
    simprr
    #
    oveq12d
    @26
    @6
    @14
    @9
    @16
    @26
    @3
    @5
    @13
    @26
    @0
    cX
    @1
    cY
    @4
    @27
    @28
    oveq12d
    fveq1d
    @26
    @3
    @8
    @15
    @26
    @0
    cX
    @1
    cY
    @7
    @27
    @28
    oveq12d
    fveq1d
    opeq12d
    mpteq12dv
    prf1.x
    prf2.y
    @18
    cvv
    wcel
    wph
    vh
    @12
    @17
    cX
    cY
    cH
    ovex
    mptex
    a1i
    ovmpt2d
end
