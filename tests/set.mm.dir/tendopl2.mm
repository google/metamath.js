include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "ccom.mm"
include "co.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "tendopl.mm"
include "3adant3.mm"
include "fveq2.mm"
include "coeq12d.mm"
include "adantl.mm"
include "simp3.mm"
include "fvex.mm"
include "coex.mm"
include "a1i.mm"
include "fvmptd.mm"

theorem tendopl2
  let vt: setvar t
  let cP: class P
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cE: class E
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vg: setvar g
  assume tendoplcbv.p: |- P = ( s e. E , t e. E |-> ( f e. T |-> ( ( s ` f ) o. ( t ` f ) ) ) )
  assume tendopl2.t: |- T = ( ( LTrn ` K ) ` W )

  disjoint s t
  disjoint E s
  disjoint E t
  disjoint f s
  disjoint f t
  disjoint T f
  disjoint T s
  disjoint T t
  disjoint W f
  disjoint W s
  disjoint W t
  disjoint s u
  disjoint s v
  disjoint t u
  disjoint t v
  disjoint u v
  disjoint E u
  disjoint E v
  disjoint f g
  disjoint f u
  disjoint f v
  disjoint g s
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint T g
  disjoint T u
  disjoint T v
  disjoint W g
  disjoint W u
  disjoint W v
  disjoint U g
  disjoint U u
  disjoint U v
  disjoint V g
  disjoint V u
  disjoint V v
  disjoint E g
  disjoint F g
  assert |- ( ( U e. E /\ V e. E /\ F e. T ) -> ( ( U P V ) ` F ) = ( ( U ` F ) o. ( V ` F ) ) )

  proof
    cU
    cE
    wcel
    #
    cV
    cE
    wcel
    #
    cF
    cT
    wcel
    #
    w3a
    #
    vg
    cF
    vg
    cv
    #
    cU
    cfv
    #
    @4
    cV
    cfv
    #
    ccom
    #
    cF
    cU
    cfv
    #
    cF
    cV
    cfv
    #
    ccom
    #
    cT
    cU
    cV
    cP
    co
    #
    cvv
    @0
    @1
    @11
    vg
    cT
    @7
    cmpt
    wceq
    @2
    vt
    cP
    cT
    cU
    vf
    vg
    cE
    cK
    cV
    cW
    vs
    tendoplcbv.p
    tendopl2.t
    tendopl
    3adant3
    @4
    cF
    wceq
    #
    @7
    @10
    wceq
    @3
    @12
    @5
    @8
    @6
    @9
    @4
    cF
    cU
    fveq2
    @4
    cF
    cV
    fveq2
    coeq12d
    adantl
    @0
    @1
    @2
    simp3
    @10
    cvv
    wcel
    @3
    @8
    @9
    cF
    cU
    fvex
    cF
    cV
    fvex
    coex
    a1i
    fvmptd
end
