include "cv.mm"
include "cdif.mm"
include "cfn.mm"
include "wcel.mm"
include "wn.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "cpw.mm"
include "crab.mm"
include "difeq2.mm"
include "eleq1d.mm"
include "notbid.mm"
include "eqeq1.mm"
include "orbi12d.mm"
include "cbvrabv.mm"
include "eqtri.mm"
include "topdifinffinlem.mm"

theorem topdifinffin
  let vx: setvar x
  let cA: class A
  let cT: class T
  let vy: setvar y
  assume topdifinf.t: |- T = { x e. ~P A | ( -. ( A \ x ) e. Fin \/ ( x = (/) \/ x = A ) ) }

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint T y
  assert |- ( T e. ( TopOn ` A ) -> A e. Fin )

  proof
    vy
    cA
    cT
    cT
    cA
    vx
    cv
    #
    cdif
    #
    cfn
    wcel
    #
    wn
    #
    @0
    c0
    wceq
    #
    @0
    cA
    wceq
    #
    wo
    #
    wo
    #
    vx
    cA
    cpw
    #
    crab
    cA
    vy
    cv
    #
    cdif
    #
    cfn
    wcel
    #
    wn
    #
    @9
    c0
    wceq
    #
    @9
    cA
    wceq
    #
    wo
    #
    wo
    #
    vy
    @8
    crab
    topdifinf.t
    @7
    @16
    vx
    vy
    @8
    @0
    @9
    wceq
    #
    @3
    @12
    @6
    @15
    @17
    @2
    @11
    @17
    @1
    @10
    cfn
    @0
    @9
    cA
    difeq2
    eleq1d
    notbid
    @17
    @4
    @13
    @5
    @14
    @0
    @9
    c0
    eqeq1
    @0
    @9
    cA
    eqeq1
    orbi12d
    orbi12d
    cbvrabv
    eqtri
    topdifinffinlem
end
