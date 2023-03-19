include "wlim.mm"
include "word.mm"
include "c0.mm"
include "wne.mm"
include "cuni.mm"
include "wceq.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "csuc.mm"
include "con0.mm"
include "wrex.mm"
include "wo.mm"
include "wn.mm"
include "df-lim.mm"
include "3anass.mm"
include "wb.mm"
include "df-ne.mm"
include "a1i.mm"
include "orduninsuc.mm"
include "anbi12d.mm"
include "ioran.mm"
include "syl6bbr.mm"
include "pm5.32i.mm"
include "3bitri.mm"

theorem dflim3
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( Lim A <-> ( Ord A /\ -. ( A = (/) \/ E. x e. On A = suc x ) ) )

  proof
    cA
    wlim
    cA
    word
    #
    cA
    c0
    wne
    #
    cA
    cA
    cuni
    wceq
    #
    w3a
    @0
    @1
    @2
    wa
    #
    wa
    @0
    cA
    c0
    wceq
    #
    cA
    vx
    cv
    csuc
    wceq
    vx
    con0
    wrex
    #
    wo
    wn
    #
    wa
    cA
    df-lim
    @0
    @1
    @2
    3anass
    @0
    @3
    @6
    @0
    @3
    @4
    wn
    #
    @5
    wn
    #
    wa
    @6
    @0
    @1
    @7
    @2
    @8
    @1
    @7
    wb
    @0
    cA
    c0
    df-ne
    a1i
    vx
    cA
    orduninsuc
    anbi12d
    @4
    @5
    ioran
    syl6bbr
    pm5.32i
    3bitri
end
