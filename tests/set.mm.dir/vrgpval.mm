include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "c0.mm"
include "cop.mm"
include "cs1.mm"
include "cec.mm"
include "cmpt.mm"
include "vrgpfval.mm"
include "fveq1d.mm"
include "wceq.mm"
include "opeq1.mm"
include "s1eqd.mm"
include "eceq1d.mm"
include "eqid.mm"
include "cvv.mm"
include "cefg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ecexg.mm"
include "ax-mp.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem vrgpval
  let cA: class A
  let c.sm: class .~
  let cU: class U
  let cI: class I
  let cV: class V
  let vj: setvar j
  let vi: setvar i
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  assume vrgpfval.r: |- .~ = ( ~FG ` I )
  assume vrgpfval.u: |- U = ( varFGrp ` I )


  assert |- ( ( I e. V /\ A e. I ) -> ( U ` A ) = [ <" <. A , (/) >. "> ] .~ )

  proof
    cI
    cV
    wcel
    #
    cA
    cI
    wcel
    cA
    cU
    cfv
    cA
    vj
    cI
    vj
    cv
    #
    c0
    cop
    #
    cs1
    #
    c.sm
    cec
    #
    cmpt
    #
    cfv
    cA
    c0
    cop
    #
    cs1
    #
    c.sm
    cec
    #
    @0
    cA
    cU
    @5
    c.sm
    cU
    vj
    cI
    cV
    vrgpfval.r
    vrgpfval.u
    vrgpfval
    fveq1d
    vj
    cA
    @4
    @8
    cI
    @5
    @1
    cA
    wceq
    #
    @3
    @7
    c.sm
    @9
    @2
    @6
    @1
    cA
    c0
    opeq1
    s1eqd
    eceq1d
    @5
    eqid
    c.sm
    cvv
    wcel
    @8
    cvv
    wcel
    c.sm
    cI
    cefg
    cfv
    cvv
    vrgpfval.r
    cI
    cefg
    fvex
    eqeltri
    @7
    cvv
    c.sm
    ecexg
    ax-mp
    fvmpt
    sylan9eq
end
