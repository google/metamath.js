include "cgch.mm"
include "wcel.mm"
include "cfn.mm"
include "cv.mm"
include "csdm.mm"
include "wbr.mm"
include "cpw.mm"
include "wa.mm"
include "wn.mm"
include "wal.mm"
include "cab.mm"
include "wo.mm"
include "cun.mm"
include "df-gch.mm"
include "eleq2i.mm"
include "elun.mm"
include "bitri.mm"
include "wceq.mm"
include "breq1.mm"
include "pweq.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "notbid.mm"
include "albidv.mm"
include "elabg.mm"
include "orbi2d.mm"
include "syl5bb.mm"

theorem elgch
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y
  let cB: class B

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B x
  assert |- ( A e. V -> ( A e. GCH <-> ( A e. Fin \/ A. x -. ( A ~< x /\ x ~< ~P A ) ) ) )

  proof
    cA
    cgch
    wcel
    #
    cA
    cfn
    wcel
    #
    cA
    vy
    cv
    #
    vx
    cv
    #
    csdm
    wbr
    #
    @3
    @2
    cpw
    #
    csdm
    wbr
    #
    wa
    #
    wn
    #
    vx
    wal
    #
    vy
    cab
    #
    wcel
    #
    wo
    #
    cA
    cV
    wcel
    #
    @1
    cA
    @3
    csdm
    wbr
    #
    @3
    cA
    cpw
    #
    csdm
    wbr
    #
    wa
    #
    wn
    #
    vx
    wal
    #
    wo
    @0
    cA
    cfn
    @10
    cun
    #
    wcel
    @12
    cgch
    @20
    cA
    vy
    vx
    df-gch
    eleq2i
    cA
    cfn
    @10
    elun
    bitri
    @13
    @11
    @19
    @1
    @9
    @19
    vy
    cA
    cV
    @2
    cA
    wceq
    #
    @8
    @18
    vx
    @21
    @7
    @17
    @21
    @4
    @14
    @6
    @16
    @2
    cA
    @3
    csdm
    breq1
    @21
    @5
    @15
    @3
    csdm
    @2
    cA
    pweq
    breq2d
    anbi12d
    notbid
    albidv
    elabg
    orbi2d
    syl5bb
end
