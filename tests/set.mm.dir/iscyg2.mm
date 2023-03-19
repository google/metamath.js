include "ccyg.mm"
include "wcel.mm"
include "cgrp.mm"
include "cz.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "iscyg.mm"
include "crab.mm"
include "neeq1i.mm"
include "rabn0.mm"
include "bitri.mm"
include "anbi2i.mm"
include "bitr4i.mm"

theorem iscyg2
  let vx: setvar x
  let cB: class B
  let c.x: class .x.
  let vn: setvar n
  let cE: class E
  let cG: class G
  let vg: setvar g
  let vm: setvar m
  let vy: setvar y
  let cN: class N
  let cO: class O
  let cX: class X
  let wph: wff ph
  assume iscyg.1: |- B = ( Base ` G )
  assume iscyg.2: |- .x. = ( .g ` G )
  assume iscyg3.e: |- E = { x e. B | ran ( n e. ZZ |-> ( n .x. x ) ) = B }

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
  assert |- ( G e. CycGrp <-> ( G e. Grp /\ E =/= (/) ) )

  proof
    cG
    ccyg
    wcel
    cG
    cgrp
    wcel
    #
    vn
    cz
    vn
    cv
    vx
    cv
    c.x
    co
    cmpt
    crn
    cB
    wceq
    #
    vx
    cB
    wrex
    #
    wa
    @0
    cE
    c0
    wne
    #
    wa
    vx
    cB
    c.x
    vn
    cG
    iscyg.1
    iscyg.2
    iscyg
    @3
    @2
    @0
    @3
    @1
    vx
    cB
    crab
    #
    c0
    wne
    @2
    cE
    @4
    c0
    iscyg3.e
    neeq1i
    @1
    vx
    cB
    rabn0
    bitri
    anbi2i
    bitr4i
end
