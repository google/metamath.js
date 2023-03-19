include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wa.mm"
include "cz.mm"
include "crio.mm"
include "cr.mm"
include "cceil.mm"
include "wceq.mm"
include "breq1.mm"
include "oveq1.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "riotabidv.mm"
include "dfceil2.mm"
include "riotaex.mm"
include "fvmpt.mm"

theorem ceilval2
  let vy: setvar y
  let cA: class A
  let vx: setvar x

  disjoint A y
  disjoint x y
  disjoint A x
  assert |- ( A e. RR -> ( |^ ` A ) = ( iota_ y e. ZZ ( A <_ y /\ y < ( A + 1 ) ) ) )

  proof
    vx
    cA
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    @1
    @0
    c1
    caddc
    co
    #
    clt
    wbr
    #
    wa
    #
    vy
    cz
    crio
    cA
    @1
    cle
    wbr
    #
    @1
    cA
    c1
    caddc
    co
    #
    clt
    wbr
    #
    wa
    #
    vy
    cz
    crio
    cr
    cceil
    @0
    cA
    wceq
    #
    @5
    @9
    vy
    cz
    @10
    @2
    @6
    @4
    @8
    @0
    cA
    @1
    cle
    breq1
    @10
    @3
    @7
    @1
    clt
    @0
    cA
    c1
    caddc
    oveq1
    breq2d
    anbi12d
    riotabidv
    vx
    vy
    dfceil2
    @9
    vy
    cz
    riotaex
    fvmpt
end
