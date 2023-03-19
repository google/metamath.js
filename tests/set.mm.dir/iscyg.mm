include "cz.mm"
include "cv.mm"
include "cmg.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "cbs.mm"
include "wceq.mm"
include "wrex.mm"
include "cgrp.mm"
include "ccyg.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveqd.mm"
include "mpteq2dv.mm"
include "rneqd.mm"
include "eqeq12d.mm"
include "rexeqbidv.mm"
include "df-cyg.mm"
include "elrab2.mm"

theorem iscyg
  let vx: setvar x
  let cB: class B
  let c.x: class .x.
  let vn: setvar n
  let cG: class G
  let vg: setvar g
  let vm: setvar m
  let vy: setvar y
  let cE: class E
  let cN: class N
  let cO: class O
  let cX: class X
  let wph: wff ph
  assume iscyg.1: |- B = ( Base ` G )
  assume iscyg.2: |- .x. = ( .g ` G )

  disjoint n x
  disjoint B n
  disjoint B x
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
  disjoint X n
  disjoint X x
  disjoint X y
  disjoint G g
  disjoint G m
  disjoint G y
  disjoint ph y
  disjoint .x. g
  disjoint .x. m
  disjoint .x. y
  assert |- ( G e. CycGrp <-> ( G e. Grp /\ E. x e. B ran ( n e. ZZ |-> ( n .x. x ) ) = B ) )

  proof
    vn
    cz
    vn
    cv
    #
    vx
    cv
    #
    vg
    cv
    #
    cmg
    cfv
    #
    co
    #
    cmpt
    #
    crn
    #
    @2
    cbs
    cfv
    #
    wceq
    #
    vx
    @7
    wrex
    vn
    cz
    @0
    @1
    c.x
    co
    #
    cmpt
    #
    crn
    #
    cB
    wceq
    #
    vx
    cB
    wrex
    vg
    cG
    cgrp
    ccyg
    @2
    cG
    wceq
    #
    @8
    @12
    vx
    @7
    cB
    @13
    @7
    cG
    cbs
    cfv
    cB
    @2
    cG
    cbs
    fveq2
    iscyg.1
    syl6eqr
    #
    @13
    @6
    @11
    @7
    cB
    @13
    @5
    @10
    @13
    vn
    cz
    @4
    @9
    @13
    @3
    c.x
    @0
    @1
    @13
    @3
    cG
    cmg
    cfv
    c.x
    @2
    cG
    cmg
    fveq2
    iscyg.2
    syl6eqr
    oveqd
    mpteq2dv
    rneqd
    @14
    eqeq12d
    rexeqbidv
    vx
    vg
    vn
    df-cyg
    elrab2
end
