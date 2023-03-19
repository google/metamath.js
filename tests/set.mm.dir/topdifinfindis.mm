include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "cpr.mm"
include "nfv.mm"
include "cv.mm"
include "cdif.mm"
include "wn.mm"
include "wceq.mm"
include "wo.mm"
include "cpw.mm"
include "crab.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "nfcv.mm"
include "wa.mm"
include "wi.mm"
include "0elpw.mm"
include "eleq1a.mm"
include "mp1i.mm"
include "pwidg.mm"
include "syl.mm"
include "jaod.mm"
include "pm4.71rd.mm"
include "wb.mm"
include "vex.mm"
include "elpr.mm"
include "a1i.mm"
include "diffi.mm"
include "biortn.mm"
include "anbi2d.mm"
include "rabeq2i.mm"
include "syl6rbbr.mm"
include "3bitr4rd.mm"
include "eqrd.mm"

theorem topdifinfindis
  let vx: setvar x
  let cA: class A
  let cT: class T
  assume topdifinf.t: |- T = { x e. ~P A | ( -. ( A \ x ) e. Fin \/ ( x = (/) \/ x = A ) ) }

  disjoint A x
  assert |- ( A e. Fin -> T = { (/) , A } )

  proof
    cA
    cfn
    wcel
    #
    vx
    cT
    c0
    cA
    cpr
    #
    @0
    vx
    nfv
    vx
    cT
    cA
    vx
    cv
    #
    cdif
    cfn
    wcel
    #
    wn
    @2
    c0
    wceq
    #
    @2
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
    topdifinf.t
    @7
    vx
    @8
    nfrab1
    nfcxfr
    vx
    @1
    nfcv
    @0
    @6
    @2
    @8
    wcel
    #
    @6
    wa
    #
    @2
    @1
    wcel
    #
    @2
    cT
    wcel
    #
    @0
    @6
    @9
    @0
    @4
    @9
    @5
    c0
    @8
    wcel
    @4
    @9
    wi
    @0
    cA
    0elpw
    c0
    @8
    @2
    eleq1a
    mp1i
    @0
    cA
    @8
    wcel
    @5
    @9
    wi
    cA
    cfn
    pwidg
    cA
    @8
    @2
    eleq1a
    syl
    jaod
    pm4.71rd
    @11
    @6
    wb
    @0
    @2
    c0
    cA
    vx
    vex
    elpr
    a1i
    @0
    @10
    @9
    @7
    wa
    @12
    @0
    @6
    @7
    @9
    @0
    @3
    @6
    @7
    wb
    cA
    @2
    diffi
    @3
    @6
    biortn
    syl
    anbi2d
    @7
    vx
    cT
    @8
    topdifinf.t
    rabeq2i
    syl6rbbr
    3bitr4rd
    eqrd
end
