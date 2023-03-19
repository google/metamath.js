include "cv.mm"
include "c0r.mm"
include "cop.mm"
include "cltrr.mm"
include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "wb.mm"
include "cnr.mm"
include "cr.mm"
include "elreal.mm"
include "breq1.mm"
include "eqeq1.mm"
include "breq2.mm"
include "orbi12d.mm"
include "notbid.mm"
include "bibi12d.mm"
include "eqeq2.mm"
include "wcel.mm"
include "wa.mm"
include "cltr.mm"
include "wor.mm"
include "ltsosr.mm"
include "sotric.mm"
include "mpan.mm"
include "ltresr.mm"
include "vex.mm"
include "eqresr.mm"
include "orbi12i.mm"
include "notbii.mm"
include "3bitr4g.mm"
include "2gencl.mm"

theorem axpre-lttri
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A <RR B <-> -. ( A = B \/ B <RR A ) ) )

  proof
    vx
    cv
    #
    c0r
    cop
    #
    vy
    cv
    #
    c0r
    cop
    #
    cltrr
    wbr
    #
    @1
    @3
    wceq
    #
    @3
    @1
    cltrr
    wbr
    #
    wo
    #
    wn
    #
    wb
    cA
    @3
    cltrr
    wbr
    #
    cA
    @3
    wceq
    #
    @3
    cA
    cltrr
    wbr
    #
    wo
    #
    wn
    #
    wb
    cA
    cB
    cltrr
    wbr
    #
    cA
    cB
    wceq
    #
    cB
    cA
    cltrr
    wbr
    #
    wo
    #
    wn
    #
    wb
    vx
    vy
    @1
    @3
    cA
    cB
    cnr
    cr
    vx
    cA
    elreal
    vy
    cB
    elreal
    @1
    cA
    wceq
    #
    @4
    @9
    @8
    @13
    @1
    cA
    @3
    cltrr
    breq1
    @19
    @7
    @12
    @19
    @5
    @10
    @6
    @11
    @1
    cA
    @3
    eqeq1
    @1
    cA
    @3
    cltrr
    breq2
    orbi12d
    notbid
    bibi12d
    @3
    cB
    wceq
    #
    @9
    @14
    @13
    @18
    @3
    cB
    cA
    cltrr
    breq2
    @20
    @12
    @17
    @20
    @10
    @15
    @11
    @16
    @3
    cB
    cA
    eqeq2
    @3
    cB
    cA
    cltrr
    breq1
    orbi12d
    notbid
    bibi12d
    @0
    cnr
    wcel
    @2
    cnr
    wcel
    wa
    #
    @0
    @2
    cltr
    wbr
    #
    @0
    @2
    wceq
    #
    @2
    @0
    cltr
    wbr
    #
    wo
    #
    wn
    #
    @4
    @8
    cnr
    cltr
    wor
    @21
    @22
    @26
    wb
    ltsosr
    cnr
    @0
    @2
    cltr
    sotric
    mpan
    @0
    @2
    ltresr
    @7
    @25
    @5
    @23
    @6
    @24
    @0
    @2
    vx
    vex
    eqresr
    @2
    @0
    ltresr
    orbi12i
    notbii
    3bitr4g
    2gencl
end
