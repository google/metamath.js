include "cv.mm"
include "wss.mm"
include "cufil.mm"
include "cfv.mm"
include "wrex.mm"
include "cfil.mm"
include "wral.mm"
include "cufl.mm"
include "wceq.mm"
include "fveq2.mm"
include "rexeqdv.mm"
include "raleqbidv.mm"
include "df-ufl.mm"
include "elab2g.mm"

theorem isufl
  let vf: setvar f
  let vg: setvar g
  let cV: class V
  let cX: class X
  let cF: class F
  let vu: setvar u
  let vx: setvar x
  let cY: class Y

  disjoint f g
  disjoint X f
  disjoint X g
  disjoint F f
  disjoint F g
  disjoint f u
  disjoint f x
  disjoint g u
  disjoint g x
  disjoint u x
  disjoint X u
  disjoint X x
  disjoint Y f
  disjoint Y g
  disjoint Y u
  assert |- ( X e. V -> ( X e. UFL <-> A. f e. ( Fil ` X ) E. g e. ( UFil ` X ) f C_ g ) )

  proof
    vf
    cv
    vg
    cv
    wss
    #
    vg
    vx
    cv
    #
    cufil
    cfv
    #
    wrex
    #
    vf
    @1
    cfil
    cfv
    #
    wral
    @0
    vg
    cX
    cufil
    cfv
    #
    wrex
    #
    vf
    cX
    cfil
    cfv
    #
    wral
    vx
    cX
    cufl
    cV
    @1
    cX
    wceq
    #
    @3
    @6
    vf
    @4
    @7
    @1
    cX
    cfil
    fveq2
    @8
    @0
    vg
    @2
    @5
    @1
    cX
    cufil
    fveq2
    rexeqdv
    raleqbidv
    vx
    vf
    vg
    df-ufl
    elab2g
end
