include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "wceq.mm"
include "oveq1.mm"
include "mpteq2dv.mm"
include "cbs.mm"
include "cfv.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"

theorem grplactfval
  let cA: class A
  let c.pl: class .+
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let cI: class I
  let cB: class B
  assume grplact.1: |- F = ( g e. X |-> ( a e. X |-> ( g .+ a ) ) )
  assume grplact.2: |- X = ( Base ` G )

  disjoint a g
  disjoint A a
  disjoint A g
  disjoint G a
  disjoint G g
  disjoint .+ a
  disjoint .+ g
  disjoint X a
  disjoint X g
  disjoint a b
  disjoint b g
  disjoint A b
  disjoint G b
  disjoint I a
  disjoint I b
  disjoint I g
  disjoint .+ b
  disjoint X b
  disjoint B a
  assert |- ( A e. X -> ( F ` A ) = ( a e. X |-> ( A .+ a ) ) )

  proof
    vg
    cA
    va
    cX
    vg
    cv
    #
    va
    cv
    #
    c.pl
    co
    #
    cmpt
    va
    cX
    cA
    @1
    c.pl
    co
    #
    cmpt
    cX
    cF
    @0
    cA
    wceq
    va
    cX
    @2
    @3
    @0
    cA
    @1
    c.pl
    oveq1
    mpteq2dv
    grplact.1
    va
    cX
    @3
    cX
    cG
    cbs
    cfv
    cvv
    grplact.2
    cG
    cbs
    fvex
    eqeltri
    mptex
    fvmpt
end
