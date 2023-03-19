include "cch.mm"
include "wcel.mm"
include "wss.mm"
include "wn.mm"
include "cv.mm"
include "wa.mm"
include "cat.mm"
include "wrex.mm"
include "wb.mm"
include "chil.mm"
include "cif.mm"
include "wceq.mm"
include "sseq1.mm"
include "notbid.mm"
include "sseq2.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "bibi12d.mm"
include "anbi2d.mm"
include "ifchhv.mm"
include "chrelat2i.mm"
include "dedth2h.mm"

theorem chrelat2
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A e. CH /\ B e. CH ) -> ( -. A C_ B <-> E. x e. HAtoms ( x C_ A /\ -. x C_ B ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    cA
    cB
    wss
    #
    wn
    #
    vx
    cv
    #
    cA
    wss
    #
    @4
    cB
    wss
    #
    wn
    #
    wa
    #
    vx
    cat
    wrex
    #
    wb
    @0
    cA
    chil
    cif
    #
    cB
    wss
    #
    wn
    #
    @4
    @10
    wss
    #
    @7
    wa
    #
    vx
    cat
    wrex
    #
    wb
    @10
    @1
    cB
    chil
    cif
    #
    wss
    #
    wn
    #
    @13
    @4
    @16
    wss
    #
    wn
    #
    wa
    #
    vx
    cat
    wrex
    #
    wb
    cA
    cB
    chil
    chil
    cA
    @10
    wceq
    #
    @3
    @12
    @9
    @15
    @23
    @2
    @11
    cA
    @10
    cB
    sseq1
    notbid
    @23
    @8
    @14
    vx
    cat
    @23
    @5
    @13
    @7
    cA
    @10
    @4
    sseq2
    anbi1d
    rexbidv
    bibi12d
    cB
    @16
    wceq
    #
    @12
    @18
    @15
    @22
    @24
    @11
    @17
    cB
    @16
    @10
    sseq2
    notbid
    @24
    @14
    @21
    vx
    cat
    @24
    @7
    @20
    @13
    @24
    @6
    @19
    cB
    @16
    @4
    sseq2
    notbid
    anbi2d
    rexbidv
    bibi12d
    vx
    @10
    @16
    cA
    ifchhv
    cB
    ifchhv
    chrelat2i
    dedth2h
end
