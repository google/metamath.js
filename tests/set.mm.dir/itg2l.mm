include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "citg1.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cdm.mm"
include "wrex.mm"
include "cab.mm"
include "eleq2i.mm"
include "cvv.mm"
include "simpr.mm"
include "fvex.mm"
include "syl6eqel.mm"
include "rexlimivw.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "elab3.mm"
include "bitri.mm"

theorem itg2l
  let vx: setvar x
  let cA: class A
  let vg: setvar g
  let cF: class F
  let cL: class L
  let vf: setvar f
  let cG: class G
  assume itg2val.1: |- L = { x | E. g e. dom S.1 ( g oR <_ F /\ x = ( S.1 ` g ) ) }

  disjoint g x
  disjoint A g
  disjoint A x
  disjoint F g
  disjoint F x
  disjoint f g
  disjoint f x
  disjoint F f
  disjoint G g
  disjoint G x
  disjoint L f
  assert |- ( A e. L <-> E. g e. dom S.1 ( g oR <_ F /\ A = ( S.1 ` g ) ) )

  proof
    cA
    cL
    wcel
    cA
    vg
    cv
    #
    cF
    cle
    cofr
    wbr
    #
    vx
    cv
    #
    @0
    citg1
    cfv
    #
    wceq
    #
    wa
    #
    vg
    citg1
    cdm
    #
    wrex
    #
    vx
    cab
    #
    wcel
    @1
    cA
    @3
    wceq
    #
    wa
    #
    vg
    @6
    wrex
    #
    cL
    @8
    cA
    itg2val.1
    eleq2i
    @7
    @11
    vx
    cA
    @10
    cA
    cvv
    wcel
    vg
    @6
    @10
    cA
    @3
    cvv
    @1
    @9
    simpr
    @0
    citg1
    fvex
    syl6eqel
    rexlimivw
    @2
    cA
    wceq
    #
    @5
    @10
    vg
    @6
    @12
    @4
    @9
    @1
    @2
    cA
    @3
    eqeq1
    anbi2d
    rexbidv
    elab3
    bitri
end
