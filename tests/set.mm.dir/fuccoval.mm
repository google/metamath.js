include "cv.mm"
include "cfv.mm"
include "c1st.mm"
include "cop.mm"
include "co.mm"
include "cvv.mm"
include "fucco.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "fveq2d.mm"
include "opeq12d.mm"
include "oveq12d.mm"
include "oveq123d.mm"
include "ovexd.mm"
include "fvmptd.mm"

theorem fuccoval
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cH: class H
  let cN: class N
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vv: setvar v
  let vx: setvar x
  assume fucco.q: |- Q = ( C FuncCat D )
  assume fucco.n: |- N = ( C Nat D )
  assume fucco.a: |- A = ( Base ` C )
  assume fucco.o: |- .x. = ( comp ` D )
  assume fucco.x: |- .xb = ( comp ` Q )
  assume fucco.f: |- ( ph -> R e. ( F N G ) )
  assume fucco.g: |- ( ph -> S e. ( G N H ) )
  assume fuccoval.f: |- ( ph -> X e. A )


  assert |- ( ph -> ( ( S ( <. F , G >. .xb H ) R ) ` X ) = ( ( S ` X ) ( <. ( ( 1st ` F ) ` X ) , ( ( 1st ` G ) ` X ) >. .x. ( ( 1st ` H ) ` X ) ) ( R ` X ) ) )

  proof
    wph
    vx
    cX
    vx
    cv
    #
    cS
    cfv
    #
    @0
    cR
    cfv
    #
    @0
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
    @0
    cH
    c1st
    cfv
    #
    cfv
    #
    c.x
    co
    #
    co
    cX
    cS
    cfv
    #
    cX
    cR
    cfv
    #
    cX
    @3
    cfv
    #
    cX
    @5
    cfv
    #
    cop
    #
    cX
    @8
    cfv
    #
    c.x
    co
    #
    co
    cA
    cS
    cR
    cF
    cG
    cop
    cH
    c.xb
    co
    co
    cvv
    wph
    vx
    cA
    cC
    cD
    cQ
    cR
    cS
    c.xb
    c.x
    cF
    cG
    cH
    cN
    fucco.q
    fucco.n
    fucco.a
    fucco.o
    fucco.x
    fucco.f
    fucco.g
    fucco
    wph
    @0
    cX
    wceq
    #
    wa
    #
    @1
    @11
    @2
    @12
    @10
    @17
    @19
    @7
    @15
    @9
    @16
    c.x
    @19
    @4
    @13
    @6
    @14
    @19
    @0
    cX
    @3
    wph
    @18
    simpr
    #
    fveq2d
    @19
    @0
    cX
    @5
    @20
    fveq2d
    opeq12d
    @19
    @0
    cX
    @8
    @20
    fveq2d
    oveq12d
    @19
    @0
    cX
    cS
    @20
    fveq2d
    @19
    @0
    cX
    cR
    @20
    fveq2d
    oveq123d
    fuccoval.f
    wph
    @11
    @12
    @17
    ovexd
    fvmptd
end
