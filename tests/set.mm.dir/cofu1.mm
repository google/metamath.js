include "ccofu.mm"
include "co.mm"
include "c1st.mm"
include "cfv.mm"
include "ccom.mm"
include "cofu1st.mm"
include "fveq1d.mm"
include "cbs.mm"
include "wf.mm"
include "wcel.mm"
include "wceq.mm"
include "c2nd.mm"
include "eqid.mm"
include "cfunc.mm"
include "wrel.mm"
include "wbr.mm"
include "relfunc.mm"
include "1st2ndbr.mm"
include "sylancr.mm"
include "funcf1.mm"
include "fvco3.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem cofu1
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cY: class Y
  assume cofuval.b: |- B = ( Base ` C )
  assume cofuval.f: |- ( ph -> F e. ( C Func D ) )
  assume cofuval.g: |- ( ph -> G e. ( D Func E ) )
  assume cofu2nd.x: |- ( ph -> X e. B )


  assert |- ( ph -> ( ( 1st ` ( G o.func F ) ) ` X ) = ( ( 1st ` G ) ` ( ( 1st ` F ) ` X ) ) )

  proof
    wph
    cX
    cG
    cF
    ccofu
    co
    c1st
    cfv
    #
    cfv
    cX
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
    cfv
    #
    cX
    @2
    cfv
    @1
    cfv
    #
    wph
    cX
    @0
    @3
    wph
    cB
    cC
    cD
    cE
    cF
    cG
    cofuval.b
    cofuval.f
    cofuval.g
    cofu1st
    fveq1d
    wph
    cB
    cD
    cbs
    cfv
    #
    @2
    wf
    cX
    cB
    wcel
    @4
    @5
    wceq
    wph
    cB
    @6
    cC
    cD
    @2
    cF
    c2nd
    cfv
    #
    cofuval.b
    @6
    eqid
    wph
    cC
    cD
    cfunc
    co
    #
    wrel
    cF
    @8
    wcel
    @2
    @7
    @8
    wbr
    cC
    cD
    relfunc
    cofuval.f
    cF
    @8
    1st2ndbr
    sylancr
    funcf1
    cofu2nd.x
    cB
    @6
    cX
    @1
    @2
    fvco3
    syl2anc
    eqtrd
end
