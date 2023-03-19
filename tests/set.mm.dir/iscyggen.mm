include "cz.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "simpl.mm"
include "oveq2d.mm"
include "mpteq2dva.mm"
include "rneqd.mm"
include "eqeq1d.mm"
include "elrab2.mm"

theorem iscyggen
  let vx: setvar x
  let cB: class B
  let c.x: class .x.
  let vn: setvar n
  let cE: class E
  let cG: class G
  let cX: class X
  let vg: setvar g
  let vm: setvar m
  let vy: setvar y
  let cN: class N
  let cO: class O
  let wph: wff ph
  assume iscyg.1: |- B = ( Base ` G )
  assume iscyg.2: |- .x. = ( .g ` G )
  assume iscyg3.e: |- E = { x e. B | ran ( n e. ZZ |-> ( n .x. x ) ) = B }

  disjoint n x
  disjoint B n
  disjoint B x
  disjoint X n
  disjoint X x
  disjoint G n
  disjoint G x
  disjoint .x. n
  disjoint .x. x
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint B g
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint B m
  disjoint n y
  disjoint x y
  disjoint B y
  disjoint E m
  disjoint E y
  disjoint N m
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint O n
  disjoint X m
  disjoint X y
  disjoint G g
  disjoint G m
  disjoint G y
  disjoint ph y
  disjoint .x. g
  disjoint .x. m
  disjoint .x. y
  assert |- ( X e. E <-> ( X e. B /\ ran ( n e. ZZ |-> ( n .x. X ) ) = B ) )

  proof
    vn
    cz
    vn
    cv
    #
    vx
    cv
    #
    c.x
    co
    #
    cmpt
    #
    crn
    #
    cB
    wceq
    vn
    cz
    @0
    cX
    c.x
    co
    #
    cmpt
    #
    crn
    #
    cB
    wceq
    vx
    cX
    cB
    cE
    @1
    cX
    wceq
    #
    @4
    @7
    cB
    @8
    @3
    @6
    @8
    vn
    cz
    @2
    @5
    @8
    @0
    cz
    wcel
    #
    wa
    @1
    cX
    @0
    c.x
    @8
    @9
    simpl
    oveq2d
    mpteq2dva
    rneqd
    eqeq1d
    iscyg3.e
    elrab2
end
