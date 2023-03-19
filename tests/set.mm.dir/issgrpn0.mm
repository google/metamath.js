include "wcel.mm"
include "cmgm.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "csgrp.mm"
include "ismgmn0.mm"
include "anbi1d.mm"
include "issgrp.mm"
include "r19.26-2.mm"
include "3bitr4g.mm"

theorem issgrpn0
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cM: class M
  let c.op: class .o.
  assume issgrpn0.b: |- B = ( Base ` M )
  assume issgrpn0.o: |- .o. = ( +g ` M )

  disjoint B x
  disjoint B y
  disjoint B z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint .o. x
  disjoint .o. y
  disjoint .o. z
  assert |- ( A e. B -> ( M e. SGrp <-> A. x e. B A. y e. B ( ( x .o. y ) e. B /\ A. z e. B ( ( x .o. y ) .o. z ) = ( x .o. ( y .o. z ) ) ) ) )

  proof
    cA
    cB
    wcel
    #
    cM
    cmgm
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    c.op
    co
    #
    vz
    cv
    #
    c.op
    co
    @2
    @3
    @5
    c.op
    co
    c.op
    co
    wceq
    vz
    cB
    wral
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    wa
    @4
    cB
    wcel
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @7
    wa
    cM
    csgrp
    wcel
    @8
    @6
    wa
    vy
    cB
    wral
    vx
    cB
    wral
    @0
    @1
    @9
    @7
    vx
    vy
    cA
    cB
    cM
    c.op
    issgrpn0.b
    issgrpn0.o
    ismgmn0
    anbi1d
    vx
    vy
    vz
    cB
    cM
    c.op
    issgrpn0.b
    issgrpn0.o
    issgrp
    @8
    @6
    vx
    vy
    cB
    cB
    r19.26-2
    3bitr4g
end
