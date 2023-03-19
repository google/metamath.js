include "wcel.mm"
include "cfrgp.mm"
include "cfv.mm"
include "cqus.mm"
include "co.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "cv.mm"
include "c2o.mm"
include "cxp.mm"
include "cfrmd.mm"
include "cefg.mm"
include "xpeq1.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "df-frgp.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "syl5eq.mm"

theorem frgpval
  let c.sm: class .~
  let cG: class G
  let cI: class I
  let cM: class M
  let cV: class V
  let vi: setvar i
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vt: setvar t
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume frgpval.m: |- G = ( freeGrp ` I )
  assume frgpval.b: |- M = ( freeMnd ` ( I X. 2o ) )
  assume frgpval.r: |- .~ = ( ~FG ` I )


  assert |- ( I e. V -> G = ( M /s .~ ) )

  proof
    cI
    cV
    wcel
    #
    cG
    cI
    cfrgp
    cfv
    #
    cM
    c.sm
    cqus
    co
    #
    frgpval.m
    @0
    cI
    cvv
    wcel
    @1
    @2
    wceq
    cI
    cV
    elex
    vi
    cI
    vi
    cv
    #
    c2o
    cxp
    #
    cfrmd
    cfv
    #
    @3
    cefg
    cfv
    #
    cqus
    co
    @2
    cvv
    cfrgp
    @3
    cI
    wceq
    #
    @5
    cM
    @6
    c.sm
    cqus
    @7
    @5
    cI
    c2o
    cxp
    #
    cfrmd
    cfv
    cM
    @7
    @4
    @8
    cfrmd
    @3
    cI
    c2o
    xpeq1
    fveq2d
    frgpval.b
    syl6eqr
    @7
    @6
    cI
    cefg
    cfv
    c.sm
    @3
    cI
    cefg
    fveq2
    frgpval.r
    syl6eqr
    oveq12d
    vi
    df-frgp
    cM
    c.sm
    cqus
    ovex
    fvmpt
    syl
    syl5eq
end
