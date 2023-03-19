include "cvv.mm"
include "wer.mm"
include "wtru.mm"
include "wrel.mm"
include "wceq.mm"
include "relopabi.mm"
include "a1i.mm"
include "cv.mm"
include "wbr.mm"
include "csb.mm"
include "id.mm"
include "eqcomd.mm"
include "eqerlem.mm"
include "3imtr4i.mm"
include "adantl.mm"
include "wa.mm"
include "eqtr.mm"
include "anbi12i.mm"
include "wcel.mm"
include "wb.mm"
include "vex.mm"
include "eqid.mm"
include "mpbir.mm"
include "2th.mm"
include "iserd.mm"
include "trud.mm"

theorem eqerOLD
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
    cvv
    cR
    wer
    wtru
    vz
    vw
    vv
    cvv
    cR
    cR
    wrel
    wtru
    cA
    cB
    wceq
    vx
    vy
    cR
    eqer.2
    relopabi
    a1i
    vz
    cv
    #
    vw
    cv
    #
    cR
    wbr
    #
    @1
    @0
    cR
    wbr
    #
    wtru
    vx
    @0
    cA
    csb
    #
    vx
    @1
    cA
    csb
    #
    wceq
    #
    @5
    @4
    wceq
    @2
    @3
    @6
    @4
    @5
    @6
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
    adantl
    @2
    @1
    vv
    cv
    #
    cR
    wbr
    #
    wa
    #
    @0
    @8
    cR
    wbr
    #
    wtru
    @6
    @5
    vx
    @8
    cA
    csb
    #
    wceq
    #
    wa
    @4
    @12
    wceq
    @10
    @11
    @4
    @5
    @12
    eqtr
    @2
    @6
    @9
    @13
    @7
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
    adantl
    @0
    cvv
    wcel
    #
    @0
    @0
    cR
    wbr
    #
    wb
    wtru
    @14
    @15
    vz
    vex
    @15
    @4
    @4
    wceq
    @4
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
    a1i
    iserd
    trud
end
