include "cv.mm"
include "cfv.mm"
include "ccnv.mm"
include "cmpt.mm"
include "wceq.mm"
include "fveq1.mm"
include "cnveqd.mm"
include "mpteq2dv.mm"
include "tendoicbv.mm"
include "cltrn.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"

theorem tendoi
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let cI: class I
  let cK: class K
  let cW: class W
  let vs: setvar s
  let vu: setvar u
  assume tendoi.i: |- I = ( s e. E |-> ( f e. T |-> `' ( s ` f ) ) )
  assume tendoi.t: |- T = ( ( LTrn ` K ) ` W )

  disjoint E s
  disjoint f g
  disjoint f s
  disjoint T f
  disjoint g s
  disjoint T g
  disjoint T s
  disjoint W f
  disjoint W g
  disjoint W s
  disjoint S g
  disjoint s u
  disjoint E u
  disjoint f u
  disjoint g u
  disjoint T u
  disjoint W u
  disjoint S u
  assert |- ( S e. E -> ( I ` S ) = ( g e. T |-> `' ( S ` g ) ) )

  proof
    vu
    cS
    vg
    cT
    vg
    cv
    #
    vu
    cv
    #
    cfv
    #
    ccnv
    #
    cmpt
    vg
    cT
    @0
    cS
    cfv
    #
    ccnv
    #
    cmpt
    cE
    cI
    @1
    cS
    wceq
    #
    vg
    cT
    @3
    @5
    @6
    @2
    @4
    @0
    @1
    cS
    fveq1
    cnveqd
    mpteq2dv
    vu
    cT
    vf
    vg
    cE
    cI
    vs
    tendoi.i
    tendoicbv
    vg
    cT
    @5
    cT
    cW
    cK
    cltrn
    cfv
    #
    cfv
    cvv
    tendoi.t
    cW
    @7
    fvex
    eqeltri
    mptex
    fvmpt
end
