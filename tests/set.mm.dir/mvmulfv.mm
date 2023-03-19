include "cv.mm"
include "co.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cvv.mm"
include "mvmulval.mm"
include "wceq.mm"
include "wa.mm"
include "oveq1.mm"
include "adantl.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "ovexd.mm"
include "fvmptd.mm"

theorem mvmulfv
  let wph: wff ph
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let vj: setvar j
  let cI: class I
  let cM: class M
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let vo: setvar o
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume mvmulfval.x: |- .X. = ( R maVecMul <. M , N >. )
  assume mvmulfval.b: |- B = ( Base ` R )
  assume mvmulfval.t: |- .x. = ( .r ` R )
  assume mvmulfval.r: |- ( ph -> R e. V )
  assume mvmulfval.m: |- ( ph -> M e. Fin )
  assume mvmulfval.n: |- ( ph -> N e. Fin )
  assume mvmulval.x: |- ( ph -> X e. ( B ^m ( M X. N ) ) )
  assume mvmulval.y: |- ( ph -> Y e. ( B ^m N ) )
  assume mvmulfv.i: |- ( ph -> I e. M )

  disjoint j ph
  disjoint M j
  disjoint N j
  disjoint R j
  disjoint X j
  disjoint Y j
  disjoint I j
  disjoint i j
  disjoint i m
  disjoint i n
  disjoint i o
  disjoint i r
  disjoint i x
  disjoint i y
  disjoint j m
  disjoint j n
  disjoint j o
  disjoint j r
  disjoint j x
  disjoint j y
  disjoint m n
  disjoint m o
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint n o
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint o r
  disjoint o x
  disjoint o y
  disjoint r x
  disjoint r y
  disjoint x y
  disjoint i ph
  disjoint o ph
  disjoint ph r
  disjoint ph x
  disjoint ph y
  disjoint M i
  disjoint M o
  disjoint M r
  disjoint M x
  disjoint M y
  disjoint N i
  disjoint N o
  disjoint N r
  disjoint N x
  disjoint N y
  disjoint R i
  disjoint R o
  disjoint R r
  disjoint R x
  disjoint R y
  disjoint B o
  disjoint B r
  disjoint B x
  disjoint B y
  disjoint .x. o
  disjoint .x. r
  disjoint .x. x
  disjoint .x. y
  disjoint .x. i
  disjoint X i
  disjoint X x
  disjoint X y
  disjoint Y i
  disjoint Y x
  disjoint Y y
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
    cM
    cX
    cY
    c.xp
    co
    cvv
    wph
    cB
    cR
    c.x
    c.xp
    vi
    vj
    cM
    cN
    cV
    cX
    cY
    mvmulfval.x
    mvmulfval.b
    mvmulfval.t
    mvmulfval.r
    mvmulfval.m
    mvmulfval.n
    mvmulval.x
    mvmulval.y
    mvmulval
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
    mvmulfv.i
    wph
    cR
    @8
    cgsu
    ovexd
    fvmptd
end
