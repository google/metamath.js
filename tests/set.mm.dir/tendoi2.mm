include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "ccnv.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "tendoi.mm"
include "adantr.mm"
include "fveq2.mm"
include "cnveqd.mm"
include "adantl.mm"
include "simpr.mm"
include "fvex.mm"
include "cnvex.mm"
include "a1i.mm"
include "fvmptd.mm"

theorem tendoi2
  let cS: class S
  let cT: class T
  let vf: setvar f
  let cE: class E
  let cF: class F
  let cI: class I
  let cK: class K
  let cW: class W
  let vs: setvar s
  let vu: setvar u
  let vg: setvar g
  assume tendoi.i: |- I = ( s e. E |-> ( f e. T |-> `' ( s ` f ) ) )
  assume tendoi.t: |- T = ( ( LTrn ` K ) ` W )

  disjoint E s
  disjoint f s
  disjoint T f
  disjoint T s
  disjoint W f
  disjoint W s
  disjoint s u
  disjoint E u
  disjoint f g
  disjoint f u
  disjoint g s
  disjoint g u
  disjoint T g
  disjoint T u
  disjoint W g
  disjoint W u
  disjoint S u
  disjoint S g
  disjoint E g
  disjoint F g
  assert |- ( ( S e. E /\ F e. T ) -> ( ( I ` S ) ` F ) = `' ( S ` F ) )

  proof
    cS
    cE
    wcel
    #
    cF
    cT
    wcel
    #
    wa
    #
    vg
    cF
    vg
    cv
    #
    cS
    cfv
    #
    ccnv
    #
    cF
    cS
    cfv
    #
    ccnv
    #
    cT
    cS
    cI
    cfv
    #
    cvv
    @0
    @8
    vg
    cT
    @5
    cmpt
    wceq
    @1
    cS
    cT
    vf
    vg
    cE
    cI
    cK
    cW
    vs
    tendoi.i
    tendoi.t
    tendoi
    adantr
    @3
    cF
    wceq
    #
    @5
    @7
    wceq
    @2
    @9
    @4
    @6
    @3
    cF
    cS
    fveq2
    cnveqd
    adantl
    @0
    @1
    simpr
    @7
    cvv
    wcel
    @2
    @6
    cF
    cS
    fvex
    cnvex
    a1i
    fvmptd
end
