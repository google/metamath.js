include "cv.mm"
include "co.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cvv.mm"
include "mavmulval.mm"
include "wceq.mm"
include "wa.mm"
include "oveq1.mm"
include "adantl.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "ovexd.mm"
include "fvmptd.mm"

theorem mavmulfv
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let vj: setvar j
  let cI: class I
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let vi: setvar i
  assume mavmulval.a: |- A = ( N Mat R )
  assume mavmulval.m: |- .X. = ( R maVecMul <. N , N >. )
  assume mavmulval.b: |- B = ( Base ` R )
  assume mavmulval.t: |- .x. = ( .r ` R )
  assume mavmulval.r: |- ( ph -> R e. V )
  assume mavmulval.n: |- ( ph -> N e. Fin )
  assume mavmulval.x: |- ( ph -> X e. ( Base ` A ) )
  assume mavmulval.y: |- ( ph -> Y e. ( B ^m N ) )
  assume mavmulfv.i: |- ( ph -> I e. N )

  disjoint N j
  disjoint R j
  disjoint X j
  disjoint Y j
  disjoint j ph
  disjoint I j
  disjoint i j
  disjoint N i
  disjoint R i
  disjoint X i
  disjoint Y i
  disjoint .x. i
  disjoint i ph
  disjoint I i
  assert |- ( ph -> ( ( X .X. Y ) ` I ) = ( R gsum ( j e. N |-> ( ( I X j ) .x. ( Y ` j ) ) ) ) )

  proof
    wph
    vi
    cI
    cR
    vj
    cN
    vi
    cv
    #
    vj
    cv
    #
    cX
    co
    #
    @1
    cY
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    cR
    vj
    cN
    cI
    @1
    cX
    co
    #
    @3
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    cN
    cX
    cY
    c.xp
    co
    cvv
    wph
    cA
    cB
    cR
    c.x
    c.xp
    vi
    vj
    cN
    cV
    cX
    cY
    mavmulval.a
    mavmulval.m
    mavmulval.b
    mavmulval.t
    mavmulval.r
    mavmulval.n
    mavmulval.x
    mavmulval.y
    mavmulval
    wph
    @0
    cI
    wceq
    #
    wa
    #
    @5
    @8
    cR
    cgsu
    @10
    vj
    cN
    @4
    @7
    @10
    @2
    @6
    @3
    c.x
    @9
    @2
    @6
    wceq
    wph
    @0
    cI
    @1
    cX
    oveq1
    adantl
    oveq1d
    mpteq2dv
    oveq2d
    mavmulfv.i
    wph
    cR
    @8
    cgsu
    ovexd
    fvmptd
end
