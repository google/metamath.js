include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "grplactfval.mm"
include "fveq1d.mm"
include "oveq2.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem grplactval
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let cI: class I
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
  disjoint B a
  disjoint a b
  disjoint b g
  disjoint A b
  disjoint G b
  disjoint I a
  disjoint I b
  disjoint I g
  disjoint .+ b
  disjoint X b
  assert |- ( ( A e. X /\ B e. X ) -> ( ( F ` A ) ` B ) = ( A .+ B ) )

  proof
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    cB
    cA
    cF
    cfv
    #
    cfv
    cB
    va
    cX
    cA
    va
    cv
    #
    c.pl
    co
    #
    cmpt
    #
    cfv
    cA
    cB
    c.pl
    co
    #
    @0
    cB
    @1
    @4
    cA
    c.pl
    vg
    cF
    cG
    cX
    va
    grplact.1
    grplact.2
    grplactfval
    fveq1d
    va
    cB
    @3
    @5
    cX
    @4
    @2
    cB
    cA
    c.pl
    oveq2
    @4
    eqid
    cA
    cB
    c.pl
    ovex
    fvmpt
    sylan9eq
end
