include "cv.mm"
include "cdif.mm"
include "cfn.mm"
include "wcel.mm"
include "wn.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "cpw.mm"
include "cin.mm"
include "disj3.mm"
include "eqcom.mm"
include "bitri.mm"
include "wb.mm"
include "wss.mm"
include "selpw.mm"
include "sseqin2.mm"
include "eqeq1.mm"
include "sylbi.mm"
include "syl5rbbr.mm"
include "wa.mm"
include "eqss.mm"
include "ssdif0.mm"
include "bicomi.mm"
include "anbi12i.mm"
include "bitr4i.mm"
include "baib.mm"
include "orbi12d.mm"
include "orcom.mm"
include "syl6bb.mm"
include "orbi2d.mm"
include "bicomd.mm"
include "rabbiia.mm"

theorem topdifinfeq
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- { x e. ~P A | ( -. ( A \ x ) e. Fin \/ ( ( A \ x ) = (/) \/ ( A \ x ) = A ) ) } = { x e. ~P A | ( -. ( A \ x ) e. Fin \/ ( x = (/) \/ x = A ) ) }

  proof
    cA
    vx
    cv
    #
    cdif
    #
    cfn
    wcel
    wn
    #
    @1
    c0
    wceq
    #
    @1
    cA
    wceq
    #
    wo
    #
    wo
    #
    @2
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
    @0
    @11
    wcel
    #
    @10
    @6
    @12
    @9
    @5
    @2
    @12
    @9
    @4
    @3
    wo
    @5
    @12
    @7
    @4
    @8
    @3
    @4
    cA
    @0
    cin
    #
    c0
    wceq
    #
    @12
    @7
    @14
    cA
    @1
    wceq
    @4
    cA
    @0
    disj3
    cA
    @1
    eqcom
    bitri
    @12
    @13
    @0
    wceq
    #
    @14
    @7
    wb
    @12
    @0
    cA
    wss
    #
    @15
    vx
    cA
    selpw
    #
    @0
    cA
    sseqin2
    bitri
    @13
    @0
    c0
    eqeq1
    sylbi
    syl5rbbr
    @8
    @12
    @3
    @8
    @16
    cA
    @0
    wss
    #
    wa
    @12
    @3
    wa
    @0
    cA
    eqss
    @12
    @16
    @3
    @18
    @17
    @18
    @3
    cA
    @0
    ssdif0
    bicomi
    anbi12i
    bitr4i
    baib
    orbi12d
    @4
    @3
    orcom
    syl6bb
    orbi2d
    bicomd
    rabbiia
end
