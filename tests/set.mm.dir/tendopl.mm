include "cv.mm"
include "cfv.mm"
include "ccom.mm"
include "cmpt.mm"
include "wceq.mm"
include "fveq1.mm"
include "coeq1d.mm"
include "mpteq2dv.mm"
include "coeq2d.mm"
include "tendoplcbv.mm"
include "cltrn.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "ovmpt2.mm"

theorem tendopl
  let vt: setvar t
  let cP: class P
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let cK: class K
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  assume tendoplcbv.p: |- P = ( s e. E , t e. E |-> ( f e. T |-> ( ( s ` f ) o. ( t ` f ) ) ) )
  assume tendopl2.t: |- T = ( ( LTrn ` K ) ` W )

  disjoint s t
  disjoint E s
  disjoint E t
  disjoint f g
  disjoint f s
  disjoint f t
  disjoint T f
  disjoint g s
  disjoint g t
  disjoint T g
  disjoint T s
  disjoint T t
  disjoint W f
  disjoint W g
  disjoint W s
  disjoint W t
  disjoint U g
  disjoint V g
  disjoint s u
  disjoint s v
  disjoint t u
  disjoint t v
  disjoint u v
  disjoint E u
  disjoint E v
  disjoint f u
  disjoint f v
  disjoint g u
  disjoint g v
  disjoint T u
  disjoint T v
  disjoint W u
  disjoint W v
  disjoint U u
  disjoint U v
  disjoint V u
  disjoint V v
  assert |- ( ( U e. E /\ V e. E ) -> ( U P V ) = ( g e. T |-> ( ( U ` g ) o. ( V ` g ) ) ) )

  proof
    vu
    vv
    cU
    cV
    cE
    cE
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
    @0
    vv
    cv
    #
    cfv
    #
    ccom
    #
    cmpt
    vg
    cT
    @0
    cU
    cfv
    #
    @0
    cV
    cfv
    #
    ccom
    #
    cmpt
    cP
    vg
    cT
    @6
    @4
    ccom
    #
    cmpt
    @1
    cU
    wceq
    #
    vg
    cT
    @5
    @9
    @10
    @2
    @6
    @4
    @0
    @1
    cU
    fveq1
    coeq1d
    mpteq2dv
    @3
    cV
    wceq
    #
    vg
    cT
    @9
    @8
    @11
    @4
    @7
    @6
    @0
    @3
    cV
    fveq1
    coeq2d
    mpteq2dv
    vv
    vu
    vt
    cP
    cT
    vf
    vg
    cE
    vs
    tendoplcbv.p
    tendoplcbv
    vg
    cT
    @8
    cT
    cW
    cK
    cltrn
    cfv
    #
    cfv
    cvv
    tendopl2.t
    cW
    @12
    fvex
    eqeltri
    mptex
    ovmpt2
end
