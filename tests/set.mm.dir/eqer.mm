include "cvv.mm"
include "wceq.mm"
include "relopabi.mm"
include "cv.mm"
include "csb.mm"
include "wbr.mm"
include "id.mm"
include "eqcomd.mm"
include "eqerlem.mm"
include "3imtr4i.mm"
include "wa.mm"
include "eqtr.mm"
include "anbi12i.mm"
include "wcel.mm"
include "vex.mm"
include "eqid.mm"
include "mpbir.mm"
include "2th.mm"
include "iseri.mm"

theorem eqer
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let vw: setvar w
  let vz: setvar z
  let vv: setvar v
  assume eqer.1: |- ( x = y -> A = B )
  assume eqer.2: |- R = { <. x , y >. | A = B }

  disjoint x y
  disjoint A y
  disjoint B x
  disjoint w x
  disjoint w y
  disjoint x z
  disjoint y z
  disjoint v x
  disjoint B v
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint w z
  disjoint R v
  disjoint R w
  disjoint R z
  assert |- R Er _V

  proof
    vz
    vw
    vv
    cvv
    cR
    cA
    cB
    wceq
    vx
    vy
    cR
    eqer.2
    relopabi
    vx
    vz
    cv
    #
    cA
    csb
    #
    vx
    vw
    cv
    #
    cA
    csb
    #
    wceq
    #
    @3
    @1
    wceq
    @0
    @2
    cR
    wbr
    #
    @2
    @0
    cR
    wbr
    @4
    @1
    @3
    @4
    id
    eqcomd
    vx
    vy
    vz
    vw
    cA
    cB
    cR
    eqer.1
    eqer.2
    eqerlem
    #
    vx
    vy
    vw
    vz
    cA
    cB
    cR
    eqer.1
    eqer.2
    eqerlem
    3imtr4i
    @4
    @3
    vx
    vv
    cv
    #
    cA
    csb
    #
    wceq
    #
    wa
    @1
    @8
    wceq
    @5
    @2
    @7
    cR
    wbr
    #
    wa
    @0
    @7
    cR
    wbr
    @1
    @3
    @8
    eqtr
    @5
    @4
    @10
    @9
    @6
    vx
    vy
    vw
    vv
    cA
    cB
    cR
    eqer.1
    eqer.2
    eqerlem
    anbi12i
    vx
    vy
    vz
    vv
    cA
    cB
    cR
    eqer.1
    eqer.2
    eqerlem
    3imtr4i
    @0
    cvv
    wcel
    @0
    @0
    cR
    wbr
    #
    vz
    vex
    @11
    @1
    @1
    wceq
    @1
    eqid
    vx
    vy
    vz
    vz
    cA
    cB
    cR
    eqer.1
    eqer.2
    eqerlem
    mpbir
    2th
    iseri
end
