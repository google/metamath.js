include "cv.mm"
include "cpw.mm"
include "wss.mm"
include "wrex.mm"
include "wa.mm"
include "wral.mm"
include "cen.mm"
include "wbr.mm"
include "wcel.mm"
include "wo.mm"
include "ctsk.mm"
include "wceq.mm"
include "sseq2.mm"
include "rexeq.mm"
include "anbi12d.mm"
include "raleqbi1dv.mm"
include "pweq.mm"
include "breq2.mm"
include "eleq2.mm"
include "orbi12d.mm"
include "raleqbidv.mm"
include "df-tsk.mm"
include "elab2g.mm"

theorem eltskg
  let vz: setvar z
  let vw: setvar w
  let cT: class T
  let cV: class V
  let cA: class A
  let vx: setvar x
  let vy: setvar y

  disjoint T w
  disjoint T z
  disjoint w z
  disjoint A x
  disjoint T x
  disjoint T y
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( T e. V -> ( T e. Tarski <-> ( A. z e. T ( ~P z C_ T /\ E. w e. T ~P z C_ w ) /\ A. z e. ~P T ( z ~~ T \/ z e. T ) ) ) )

  proof
    vz
    cv
    #
    cpw
    #
    vy
    cv
    #
    wss
    #
    @1
    vw
    cv
    wss
    #
    vw
    @2
    wrex
    #
    wa
    #
    vz
    @2
    wral
    #
    @0
    @2
    cen
    wbr
    #
    @0
    @2
    wcel
    #
    wo
    #
    vz
    @2
    cpw
    #
    wral
    #
    wa
    @1
    cT
    wss
    #
    @4
    vw
    cT
    wrex
    #
    wa
    #
    vz
    cT
    wral
    #
    @0
    cT
    cen
    wbr
    #
    @0
    cT
    wcel
    #
    wo
    #
    vz
    cT
    cpw
    #
    wral
    #
    wa
    vy
    cT
    ctsk
    cV
    @2
    cT
    wceq
    #
    @7
    @16
    @12
    @21
    @6
    @15
    vz
    @2
    cT
    @22
    @3
    @13
    @5
    @14
    @2
    cT
    @1
    sseq2
    @4
    vw
    @2
    cT
    rexeq
    anbi12d
    raleqbi1dv
    @22
    @10
    @19
    vz
    @11
    @20
    @2
    cT
    pweq
    @22
    @8
    @17
    @9
    @18
    @2
    cT
    @0
    cen
    breq2
    @2
    cT
    @0
    eleq2
    orbi12d
    raleqbidv
    anbi12d
    vy
    vz
    vw
    df-tsk
    elab2g
end
