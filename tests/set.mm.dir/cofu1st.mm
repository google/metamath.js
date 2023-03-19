include "ccofu.mm"
include "co.mm"
include "c1st.mm"
include "cfv.mm"
include "ccom.mm"
include "cv.mm"
include "c2nd.mm"
include "cmpt2.mm"
include "cop.mm"
include "cofuval.mm"
include "fveq2d.mm"
include "fvex.mm"
include "coex.mm"
include "cbs.mm"
include "cvv.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "op1st.mm"
include "syl6eq.mm"

theorem cofu1st
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  let cY: class Y
  assume cofuval.b: |- B = ( Base ` C )
  assume cofuval.f: |- ( ph -> F e. ( C Func D ) )
  assume cofuval.g: |- ( ph -> G e. ( D Func E ) )


  assert |- ( ph -> ( 1st ` ( G o.func F ) ) = ( ( 1st ` G ) o. ( 1st ` F ) ) )

  proof
    wph
    cG
    cF
    ccofu
    co
    #
    c1st
    cfv
    cG
    c1st
    cfv
    #
    cF
    c1st
    cfv
    #
    ccom
    #
    vx
    vy
    cB
    cB
    vx
    cv
    #
    @2
    cfv
    vy
    cv
    #
    @2
    cfv
    cG
    c2nd
    cfv
    co
    @4
    @5
    cF
    c2nd
    cfv
    co
    ccom
    #
    cmpt2
    #
    cop
    #
    c1st
    cfv
    @3
    wph
    @0
    @8
    c1st
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
    @3
    @7
    @1
    @2
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
    @6
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
    @9
    mpt2ex
    op1st
    syl6eq
end
