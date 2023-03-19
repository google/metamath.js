include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "co.mm"
include "cvv.mm"
include "cmpt.mm"
include "chom.mm"
include "ccid.mm"
include "cop.mm"
include "c2nd.mm"
include "cmpt2.mm"
include "wceq.mm"
include "eqid.mm"
include "curf1.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "mpt2ex.mm"
include "op1std.mm"
include "syl.mm"
include "wa.mm"
include "simpr.mm"
include "oveq2d.mm"
include "ovexd.mm"
include "fvmptd.mm"

theorem curf11
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cK: class K
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.1: class .1.
  let vh: setvar h
  let vw: setvar w
  let cH: class H
  let cI: class I
  let cZ: class Z
  let cJ: class J
  assume curfval.g: |- G = ( <. C , D >. curryF F )
  assume curfval.a: |- A = ( Base ` C )
  assume curfval.c: |- ( ph -> C e. Cat )
  assume curfval.d: |- ( ph -> D e. Cat )
  assume curfval.f: |- ( ph -> F e. ( ( C Xc. D ) Func E ) )
  assume curfval.b: |- B = ( Base ` D )
  assume curf1.x: |- ( ph -> X e. A )
  assume curf1.k: |- K = ( ( 1st ` G ) ` X )
  assume curf11.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( ( 1st ` K ) ` Y ) = ( X ( 1st ` F ) Y ) )

  proof
    wph
    vy
    cY
    cX
    vy
    cv
    #
    cF
    c1st
    cfv
    #
    co
    #
    cX
    cY
    @1
    co
    cB
    cK
    c1st
    cfv
    #
    cvv
    wph
    cK
    vy
    cB
    @2
    cmpt
    #
    vy
    vz
    cB
    cB
    vg
    @0
    vz
    cv
    #
    cD
    chom
    cfv
    #
    co
    cX
    cC
    ccid
    cfv
    #
    cfv
    vg
    cv
    cX
    @0
    cop
    cX
    @5
    cop
    cF
    c2nd
    cfv
    co
    co
    cmpt
    #
    cmpt2
    #
    cop
    wceq
    @3
    @4
    wceq
    wph
    vy
    vz
    cA
    cB
    cC
    cD
    @7
    vg
    cE
    cF
    cG
    @6
    cK
    cX
    curfval.g
    curfval.a
    curfval.c
    curfval.d
    curfval.f
    curfval.b
    curf1.x
    curf1.k
    @6
    eqid
    @7
    eqid
    curf1
    @4
    @9
    cK
    vy
    cB
    @2
    cB
    cD
    cbs
    cfv
    cvv
    curfval.b
    cD
    cbs
    fvex
    eqeltri
    #
    mptex
    vy
    vz
    cB
    cB
    @8
    @10
    @10
    mpt2ex
    op1std
    syl
    wph
    @0
    cY
    wceq
    #
    wa
    @0
    cY
    cX
    @1
    wph
    @11
    simpr
    oveq2d
    curf11.y
    wph
    cX
    cY
    @1
    ovexd
    fvmptd
end
