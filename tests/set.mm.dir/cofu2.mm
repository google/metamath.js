include "ccofu.mm"
include "co.mm"
include "c2nd.mm"
include "cfv.mm"
include "c1st.mm"
include "ccom.mm"
include "cofu2nd.mm"
include "fveq1d.mm"
include "chom.mm"
include "wf.mm"
include "wcel.mm"
include "wceq.mm"
include "eqid.mm"
include "cfunc.mm"
include "wrel.mm"
include "wbr.mm"
include "relfunc.mm"
include "1st2ndbr.mm"
include "sylancr.mm"
include "funcf2.mm"
include "fvco3.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem cofu2
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
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
  assume cofu2.h: |- H = ( Hom ` C )
  assume cofu2.y: |- ( ph -> R e. ( X H Y ) )


  assert |- ( ph -> ( ( X ( 2nd ` ( G o.func F ) ) Y ) ` R ) = ( ( ( ( 1st ` F ) ` X ) ( 2nd ` G ) ( ( 1st ` F ) ` Y ) ) ` ( ( X ( 2nd ` F ) Y ) ` R ) ) )

  proof
    wph
    cR
    cX
    cY
    cG
    cF
    ccofu
    co
    c2nd
    cfv
    co
    #
    cfv
    cR
    cX
    cF
    c1st
    cfv
    #
    cfv
    #
    cY
    @1
    cfv
    #
    cG
    c2nd
    cfv
    co
    #
    cX
    cY
    cF
    c2nd
    cfv
    #
    co
    #
    ccom
    #
    cfv
    #
    cR
    @6
    cfv
    @4
    cfv
    #
    wph
    cR
    @0
    @7
    wph
    cB
    cC
    cD
    cE
    cF
    cG
    cX
    cY
    cofuval.b
    cofuval.f
    cofuval.g
    cofu2nd.x
    cofu2nd.y
    cofu2nd
    fveq1d
    wph
    cX
    cY
    cH
    co
    #
    @2
    @3
    cD
    chom
    cfv
    #
    co
    #
    @6
    wf
    cR
    @10
    wcel
    @8
    @9
    wceq
    wph
    cB
    cC
    cD
    @1
    @5
    cH
    @11
    cX
    cY
    cofuval.b
    cofu2.h
    @11
    eqid
    wph
    cC
    cD
    cfunc
    co
    #
    wrel
    cF
    @13
    wcel
    @1
    @5
    @13
    wbr
    cC
    cD
    relfunc
    cofuval.f
    cF
    @13
    1st2ndbr
    sylancr
    cofu2nd.x
    cofu2nd.y
    funcf2
    cofu2.y
    @10
    @12
    cR
    @4
    @6
    fvco3
    syl2anc
    eqtrd
end
