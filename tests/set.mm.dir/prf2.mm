include "cv.mm"
include "c2nd.mm"
include "cfv.mm"
include "co.mm"
include "cop.mm"
include "cvv.mm"
include "prf2fval.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "fveq2d.mm"
include "opeq12d.mm"
include "wcel.mm"
include "opex.mm"
include "a1i.mm"
include "fvmptd.mm"

theorem prf2
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cX: class X
  let cY: class Y
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  assume prfval.k: |- P = ( F pairF G )
  assume prfval.b: |- B = ( Base ` C )
  assume prfval.h: |- H = ( Hom ` C )
  assume prfval.c: |- ( ph -> F e. ( C Func D ) )
  assume prfval.d: |- ( ph -> G e. ( C Func E ) )
  assume prf1.x: |- ( ph -> X e. B )
  assume prf2.y: |- ( ph -> Y e. B )
  assume prf2.k: |- ( ph -> K e. ( X H Y ) )


  assert |- ( ph -> ( ( X ( 2nd ` P ) Y ) ` K ) = <. ( ( X ( 2nd ` F ) Y ) ` K ) , ( ( X ( 2nd ` G ) Y ) ` K ) >. )

  proof
    wph
    vh
    cK
    vh
    cv
    #
    cX
    cY
    cF
    c2nd
    cfv
    co
    #
    cfv
    #
    @0
    cX
    cY
    cG
    c2nd
    cfv
    co
    #
    cfv
    #
    cop
    cK
    @1
    cfv
    #
    cK
    @3
    cfv
    #
    cop
    #
    cX
    cY
    cH
    co
    cX
    cY
    cP
    c2nd
    cfv
    co
    cvv
    wph
    cB
    cC
    cD
    cP
    vh
    cE
    cF
    cG
    cH
    cX
    cY
    prfval.k
    prfval.b
    prfval.h
    prfval.c
    prfval.d
    prf1.x
    prf2.y
    prf2fval
    wph
    @0
    cK
    wceq
    #
    wa
    #
    @2
    @5
    @4
    @6
    @9
    @0
    cK
    @1
    wph
    @8
    simpr
    #
    fveq2d
    @9
    @0
    cK
    @3
    @10
    fveq2d
    opeq12d
    prf2.k
    @7
    cvv
    wcel
    wph
    @5
    @6
    opex
    a1i
    fvmptd
end
