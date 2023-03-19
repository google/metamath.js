include "csn.mm"
include "wss.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "wcel.mm"
include "cv.mm"
include "wex.mm"
include "neq0.mm"
include "wb.mm"
include "ssel.mm"
include "elsni.mm"
include "syl6.mm"
include "eleq1.mm"
include "ibd.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "snssi.mm"
include "anc2li.mm"
include "eqss.mm"
include "syl6ibr.mm"
include "orrd.mm"
include "0ss.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "eqimss.mm"
include "jaoi.mm"
include "impbii.mm"

theorem sssn
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( A C_ { B } <-> ( A = (/) \/ A = { B } ) )

  proof
    cA
    cB
    csn
    #
    wss
    #
    cA
    c0
    wceq
    #
    cA
    @0
    wceq
    #
    wo
    @1
    @2
    @3
    @1
    @2
    wn
    #
    @1
    @0
    cA
    wss
    #
    wa
    @3
    @1
    @4
    @5
    @1
    @4
    cB
    cA
    wcel
    #
    @5
    @4
    vx
    cv
    #
    cA
    wcel
    #
    vx
    wex
    @1
    @6
    vx
    cA
    neq0
    @1
    @8
    @6
    vx
    @1
    @8
    @6
    @1
    @8
    @7
    cB
    wceq
    #
    @8
    @6
    wb
    @1
    @8
    @7
    @0
    wcel
    @9
    cA
    @0
    @7
    ssel
    @7
    cB
    elsni
    syl6
    @7
    cB
    cA
    eleq1
    syl6
    ibd
    exlimdv
    syl5bi
    cB
    cA
    snssi
    syl6
    anc2li
    cA
    @0
    eqss
    syl6ibr
    orrd
    @2
    @1
    @3
    @2
    @1
    c0
    @0
    wss
    @0
    0ss
    cA
    c0
    @0
    sseq1
    mpbiri
    cA
    @0
    eqimss
    jaoi
    impbii
end
