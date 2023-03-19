include "word.mm"
include "con0.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "cuni.mm"
include "cv.mm"
include "csuc.mm"
include "wrex.mm"
include "wn.mm"
include "wb.mm"
include "ordeleqon.mm"
include "c0.mm"
include "cif.mm"
include "id.mm"
include "unieq.mm"
include "eqeq12d.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "notbid.mm"
include "bibi12d.mm"
include "0elon.mm"
include "elimel.mm"
include "onuninsuci.mm"
include "dedth.mm"
include "unon.mm"
include "eqcomi.mm"
include "cvv.mm"
include "onprc.mm"
include "vex.mm"
include "sucex.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "mto.mm"
include "a1i.mm"
include "nrex.mm"
include "2th.mm"
include "jaoi.mm"
include "sylbi.mm"

theorem orduninsuc
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( Ord A -> ( A = U. A <-> -. E. x e. On A = suc x ) )

  proof
    cA
    word
    cA
    con0
    wcel
    #
    cA
    con0
    wceq
    #
    wo
    cA
    cA
    cuni
    #
    wceq
    #
    cA
    vx
    cv
    #
    csuc
    #
    wceq
    #
    vx
    con0
    wrex
    #
    wn
    #
    wb
    #
    cA
    ordeleqon
    @0
    @9
    @1
    @0
    @9
    @0
    cA
    c0
    cif
    #
    @10
    cuni
    #
    wceq
    #
    @10
    @5
    wceq
    #
    vx
    con0
    wrex
    #
    wn
    #
    wb
    cA
    c0
    cA
    @10
    wceq
    #
    @3
    @12
    @8
    @15
    @16
    cA
    @10
    @2
    @11
    @16
    id
    cA
    @10
    unieq
    eqeq12d
    @16
    @7
    @14
    @16
    @6
    @13
    vx
    con0
    cA
    @10
    @5
    eqeq1
    rexbidv
    notbid
    bibi12d
    vx
    @10
    cA
    c0
    con0
    0elon
    elimel
    onuninsuci
    dedth
    @1
    @9
    con0
    con0
    cuni
    #
    wceq
    #
    con0
    @5
    wceq
    #
    vx
    con0
    wrex
    #
    wn
    #
    wb
    @18
    @21
    @17
    con0
    unon
    eqcomi
    @19
    vx
    con0
    @19
    wn
    @4
    con0
    wcel
    @19
    con0
    cvv
    wcel
    #
    onprc
    @19
    @22
    @5
    cvv
    wcel
    @4
    vx
    vex
    sucex
    con0
    @5
    cvv
    eleq1
    mpbiri
    mto
    a1i
    nrex
    2th
    @1
    @3
    @18
    @8
    @21
    @1
    cA
    con0
    @2
    @17
    @1
    id
    cA
    con0
    unieq
    eqeq12d
    @1
    @7
    @20
    @1
    @6
    @19
    vx
    con0
    cA
    con0
    @5
    eqeq1
    rexbidv
    notbid
    bibi12d
    mpbiri
    jaoi
    sylbi
end
