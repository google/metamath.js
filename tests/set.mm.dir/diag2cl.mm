include "c2nd.mm"
include "cfv.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "c1st.mm"
include "diag2.mm"
include "cfuc.mm"
include "eqid.mm"
include "fuchom.mm"
include "cfunc.mm"
include "wrel.mm"
include "wcel.mm"
include "wbr.mm"
include "relfunc.mm"
include "diagcl.mm"
include "1st2ndbr.mm"
include "sylancr.mm"
include "funcf2.mm"
include "ffvelrnd.mm"
include "eqeltrrd.mm"

theorem diag2cl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cH: class H
  let cL: class L
  let cN: class N
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume diag2.l: |- L = ( C DiagFunc D )
  assume diag2.a: |- A = ( Base ` C )
  assume diag2.b: |- B = ( Base ` D )
  assume diag2.h: |- H = ( Hom ` C )
  assume diag2.c: |- ( ph -> C e. Cat )
  assume diag2.d: |- ( ph -> D e. Cat )
  assume diag2.x: |- ( ph -> X e. A )
  assume diag2.y: |- ( ph -> Y e. A )
  assume diag2.f: |- ( ph -> F e. ( X H Y ) )
  assume diag2cl.h: |- N = ( D Nat C )


  assert |- ( ph -> ( B X. { F } ) e. ( ( ( 1st ` L ) ` X ) N ( ( 1st ` L ) ` Y ) ) )

  proof
    wph
    cF
    cX
    cY
    cL
    c2nd
    cfv
    #
    co
    #
    cfv
    cB
    cF
    csn
    cxp
    cX
    cL
    c1st
    cfv
    #
    cfv
    cY
    @2
    cfv
    cN
    co
    #
    wph
    cA
    cB
    cC
    cD
    cF
    cH
    cL
    cX
    cY
    diag2.l
    diag2.a
    diag2.b
    diag2.h
    diag2.c
    diag2.d
    diag2.x
    diag2.y
    diag2.f
    diag2
    wph
    cX
    cY
    cH
    co
    @3
    cF
    @1
    wph
    cA
    cC
    cD
    cC
    cfuc
    co
    #
    @2
    @0
    cH
    cN
    cX
    cY
    diag2.a
    diag2.h
    cD
    cC
    @4
    cN
    @4
    eqid
    #
    diag2cl.h
    fuchom
    wph
    cC
    @4
    cfunc
    co
    #
    wrel
    cL
    @6
    wcel
    @2
    @0
    @6
    wbr
    cC
    @4
    relfunc
    wph
    cC
    cD
    @4
    cL
    diag2.l
    diag2.c
    diag2.d
    @5
    diagcl
    cL
    @6
    1st2ndbr
    sylancr
    diag2.x
    diag2.y
    funcf2
    diag2.f
    ffvelrnd
    eqeltrrd
end
