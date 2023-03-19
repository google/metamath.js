include "wcel.mm"
include "cvrgp.mm"
include "cfv.mm"
include "cv.mm"
include "c0.mm"
include "cop.mm"
include "cs1.mm"
include "cec.mm"
include "cmpt.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "cefg.mm"
include "id.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eceq2.mm"
include "syl.mm"
include "mpteq12dv.mm"
include "df-vrgp.mm"
include "vex.mm"
include "mptex.mm"
include "fvmpt3i.mm"
include "syl5eq.mm"

theorem vrgpfval
  let c.sm: class .~
  let cU: class U
  let vj: setvar j
  let cI: class I
  let cV: class V
  let cA: class A
  let vi: setvar i
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  assume vrgpfval.r: |- .~ = ( ~FG ` I )
  assume vrgpfval.u: |- U = ( varFGrp ` I )

  disjoint I j
  disjoint .~ j
  disjoint V j
  disjoint A j
  disjoint i j
  disjoint i x
  disjoint i y
  disjoint I i
  disjoint j x
  disjoint j y
  disjoint x y
  disjoint I x
  disjoint I y
  disjoint .~ i
  disjoint .~ x
  disjoint .~ y
  disjoint X j
  assert |- ( I e. V -> U = ( j e. I |-> [ <" <. j , (/) >. "> ] .~ ) )

  proof
    cI
    cV
    wcel
    #
    cU
    cI
    cvrgp
    cfv
    #
    vj
    cI
    vj
    cv
    c0
    cop
    cs1
    #
    c.sm
    cec
    #
    cmpt
    #
    vrgpfval.u
    @0
    cI
    cvv
    wcel
    @1
    @4
    wceq
    cI
    cV
    elex
    vi
    cI
    vj
    vi
    cv
    #
    @2
    @5
    cefg
    cfv
    #
    cec
    #
    cmpt
    @4
    cvv
    cvrgp
    @5
    cI
    wceq
    #
    vj
    @5
    @7
    cI
    @3
    @8
    id
    @8
    @6
    c.sm
    wceq
    @7
    @3
    wceq
    @8
    @6
    cI
    cefg
    cfv
    c.sm
    @5
    cI
    cefg
    fveq2
    vrgpfval.r
    syl6eqr
    @6
    c.sm
    @2
    eceq2
    syl
    mpteq12dv
    vi
    vj
    df-vrgp
    vj
    @5
    @7
    vi
    vex
    mptex
    fvmpt3i
    syl
    syl5eq
end
