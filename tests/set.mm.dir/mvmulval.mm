include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cvv.mm"
include "mvmulfval.mm"
include "wceq.mm"
include "wa.mm"
include "oveq.mm"
include "fveq1.mm"
include "oveqan12d.mm"
include "adantl.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "cfn.mm"
include "wcel.mm"
include "mptexg.mm"
include "syl.mm"
include "ovmpt2d.mm"

theorem mvmulval
  let wph: wff ph
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let vi: setvar i
  let vj: setvar j
  let cM: class M
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
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

  disjoint i j
  disjoint i ph
  disjoint j ph
  disjoint M i
  disjoint M j
  disjoint N i
  disjoint N j
  disjoint R i
  disjoint R j
  disjoint .x. i
  disjoint X i
  disjoint X j
  disjoint Y i
  disjoint Y j
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
  disjoint o ph
  disjoint ph r
  disjoint ph x
  disjoint ph y
  disjoint M o
  disjoint M r
  disjoint M x
  disjoint M y
  disjoint N o
  disjoint N r
  disjoint N x
  disjoint N y
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
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> ( X .X. Y ) = ( i e. M |-> ( R gsum ( j e. N |-> ( ( i X j ) .x. ( Y ` j ) ) ) ) ) )

  proof
    wph
    vx
    vy
    cX
    cY
    cB
    cM
    cN
    cxp
    cmap
    co
    cB
    cN
    cmap
    co
    vi
    cM
    cR
    vj
    cN
    vi
    cv
    #
    vj
    cv
    #
    vx
    cv
    #
    co
    #
    @1
    vy
    cv
    #
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    vi
    cM
    cR
    vj
    cN
    @0
    @1
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
    #
    cmpt
    #
    c.xp
    cvv
    wph
    vx
    vy
    cB
    cR
    c.x
    c.xp
    vi
    vj
    cM
    cN
    cV
    mvmulfval.x
    mvmulfval.b
    mvmulfval.t
    mvmulfval.r
    mvmulfval.m
    mvmulfval.n
    mvmulfval
    wph
    @2
    cX
    wceq
    #
    @4
    cY
    wceq
    #
    wa
    #
    wa
    #
    vi
    cM
    @8
    @13
    @18
    @7
    @12
    cR
    cgsu
    @18
    vj
    cN
    @6
    @11
    @17
    @6
    @11
    wceq
    wph
    @15
    @16
    @3
    @9
    @5
    @10
    c.x
    @0
    @1
    @2
    cX
    oveq
    @1
    @4
    cY
    fveq1
    oveqan12d
    adantl
    mpteq2dv
    oveq2d
    mpteq2dv
    mvmulval.x
    mvmulval.y
    wph
    cM
    cfn
    wcel
    @14
    cvv
    wcel
    mvmulfval.m
    vi
    cM
    @13
    cfn
    mptexg
    syl
    ovmpt2d
end
