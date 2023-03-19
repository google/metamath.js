include "cbs.mm"
include "cfv.mm"
include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "cfn.mm"
include "wcel.mm"
include "wceq.mm"
include "matbas2.mm"
include "syl2anc.mm"
include "eleqtrrd.mm"
include "mvmulval.mm"

theorem mavmulval
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let vi: setvar i
  let vj: setvar j
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  assume mavmulval.a: |- A = ( N Mat R )
  assume mavmulval.m: |- .X. = ( R maVecMul <. N , N >. )
  assume mavmulval.b: |- B = ( Base ` R )
  assume mavmulval.t: |- .x. = ( .r ` R )
  assume mavmulval.r: |- ( ph -> R e. V )
  assume mavmulval.n: |- ( ph -> N e. Fin )
  assume mavmulval.x: |- ( ph -> X e. ( Base ` A ) )
  assume mavmulval.y: |- ( ph -> Y e. ( B ^m N ) )

  disjoint i j
  disjoint N i
  disjoint N j
  disjoint R i
  disjoint R j
  disjoint X i
  disjoint X j
  disjoint Y i
  disjoint Y j
  disjoint .x. i
  disjoint i ph
  disjoint j ph
  assert |- ( ph -> ( X .X. Y ) = ( i e. N |-> ( R gsum ( j e. N |-> ( ( i X j ) .x. ( Y ` j ) ) ) ) ) )

  proof
    wph
    cB
    cR
    c.x
    c.xp
    vi
    vj
    cN
    cN
    cV
    cX
    cY
    mavmulval.m
    mavmulval.b
    mavmulval.t
    mavmulval.r
    mavmulval.n
    mavmulval.n
    wph
    cX
    cA
    cbs
    cfv
    #
    cB
    cN
    cN
    cxp
    cmap
    co
    #
    mavmulval.x
    wph
    cN
    cfn
    wcel
    cR
    cV
    wcel
    @1
    @0
    wceq
    mavmulval.n
    mavmulval.r
    cA
    cR
    cB
    cN
    cV
    mavmulval.a
    mavmulval.b
    matbas2
    syl2anc
    eleqtrrd
    mavmulval.y
    mvmulval
end
