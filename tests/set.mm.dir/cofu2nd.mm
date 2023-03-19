include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "co.mm"
include "ccom.mm"
include "ccofu.mm"
include "cvv.mm"
include "cmpt2.mm"
include "cop.mm"
include "cofuval.mm"
include "fveq2d.mm"
include "fvex.mm"
include "coex.mm"
include "cbs.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "op2nd.mm"
include "syl6eq.mm"
include "wceq.mm"
include "wa.mm"
include "simprl.mm"
include "simprr.mm"
include "oveq12d.mm"
include "coeq12d.mm"
include "wcel.mm"
include "ovex.mm"
include "a1i.mm"
include "ovmpt2d.mm"

theorem cofu2nd
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  assume cofuval.b: |- B = ( Base ` C )
  assume cofuval.f: |- ( ph -> F e. ( C Func D ) )
  assume cofuval.g: |- ( ph -> G e. ( D Func E ) )
  assume cofu2nd.x: |- ( ph -> X e. B )
  assume cofu2nd.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X ( 2nd ` ( G o.func F ) ) Y ) = ( ( ( ( 1st ` F ) ` X ) ( 2nd ` G ) ( ( 1st ` F ) ` Y ) ) o. ( X ( 2nd ` F ) Y ) ) )

  proof
    wph
    vx
    vy
    cX
    cY
    cB
    cB
    vx
    cv
    #
    cF
    c1st
    cfv
    #
    cfv
    #
    vy
    cv
    #
    @1
    cfv
    #
    cG
    c2nd
    cfv
    #
    co
    #
    @0
    @3
    cF
    c2nd
    cfv
    #
    co
    #
    ccom
    #
    cX
    @1
    cfv
    #
    cY
    @1
    cfv
    #
    @5
    co
    #
    cX
    cY
    @7
    co
    #
    ccom
    #
    cG
    cF
    ccofu
    co
    #
    c2nd
    cfv
    #
    cvv
    wph
    @16
    cG
    c1st
    cfv
    #
    @1
    ccom
    #
    vx
    vy
    cB
    cB
    @9
    cmpt2
    #
    cop
    #
    c2nd
    cfv
    @19
    wph
    @15
    @20
    c2nd
    wph
    vx
    vy
    cB
    cC
    cD
    cE
    cF
    cG
    cofuval.b
    cofuval.f
    cofuval.g
    cofuval
    fveq2d
    @18
    @19
    @17
    @1
    cG
    c1st
    fvex
    cF
    c1st
    fvex
    coex
    vx
    vy
    cB
    cB
    @9
    cB
    cC
    cbs
    cfv
    cvv
    cofuval.b
    cC
    cbs
    fvex
    eqeltri
    #
    @21
    mpt2ex
    op2nd
    syl6eq
    wph
    @0
    cX
    wceq
    #
    @3
    cY
    wceq
    #
    wa
    wa
    #
    @6
    @12
    @8
    @13
    @24
    @2
    @10
    @4
    @11
    @5
    @24
    @0
    cX
    @1
    wph
    @22
    @23
    simprl
    #
    fveq2d
    @24
    @3
    cY
    @1
    wph
    @22
    @23
    simprr
    #
    fveq2d
    oveq12d
    @24
    @0
    cX
    @3
    cY
    @7
    @25
    @26
    oveq12d
    coeq12d
    cofu2nd.x
    cofu2nd.y
    @14
    cvv
    wcel
    wph
    @12
    @13
    @10
    @11
    @5
    ovex
    cX
    cY
    @7
    ovex
    coex
    a1i
    ovmpt2d
end
