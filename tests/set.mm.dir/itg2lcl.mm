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
include "cxr.mm"
include "wcel.mm"
include "itg1cl.mm"
include "rexrd.mm"
include "simpr.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "rexlimiv.mm"
include "abssi.mm"
include "eqsstri.mm"

theorem itg2lcl
  let vx: setvar x
  let vg: setvar g
  let cF: class F
  let cL: class L
  let cA: class A
  let vf: setvar f
  let cG: class G
  assume itg2val.1: |- L = { x | E. g e. dom S.1 ( g oR <_ F /\ x = ( S.1 ` g ) ) }

  disjoint g x
  disjoint F g
  disjoint F x
  disjoint A g
  disjoint A x
  disjoint f g
  disjoint f x
  disjoint F f
  disjoint G g
  disjoint G x
  disjoint L f
  assert |- L C_ RR*

  proof
    cL
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
    cxr
    itg2val.1
    @7
    vx
    cxr
    @5
    @2
    cxr
    wcel
    #
    vg
    @6
    @0
    @6
    wcel
    #
    @8
    @5
    @3
    cxr
    wcel
    @9
    @3
    @0
    itg1cl
    rexrd
    @5
    @2
    @3
    cxr
    @1
    @4
    simpr
    eleq1d
    syl5ibrcom
    rexlimiv
    abssi
    eqsstri
end
