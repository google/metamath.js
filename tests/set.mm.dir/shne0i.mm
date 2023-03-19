include "c0h.mm"
include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "c0v.mm"
include "df-ne.mm"
include "wa.mm"
include "wex.mm"
include "wss.mm"
include "df-rex.mm"
include "nss.mm"
include "csh.mm"
include "wb.mm"
include "shle0.mm"
include "ax-mp.mm"
include "notbii.mm"
include "3bitr2ri.mm"
include "elch0.mm"
include "necon3bbii.mm"
include "rexbii.mm"
include "3bitri.mm"

theorem shne0i
  let vx: setvar x
  let cA: class A
  assume shne0.1: |- A e. SH

  disjoint A x
  assert |- ( A =/= 0H <-> E. x e. A x =/= 0h )

  proof
    cA
    c0h
    wne
    cA
    c0h
    wceq
    #
    wn
    #
    vx
    cv
    #
    c0h
    wcel
    #
    wn
    #
    vx
    cA
    wrex
    #
    @2
    c0v
    wne
    #
    vx
    cA
    wrex
    cA
    c0h
    df-ne
    @5
    @2
    cA
    wcel
    @4
    wa
    vx
    wex
    cA
    c0h
    wss
    #
    wn
    @1
    @4
    vx
    cA
    df-rex
    vx
    cA
    c0h
    nss
    @7
    @0
    cA
    csh
    wcel
    @7
    @0
    wb
    shne0.1
    cA
    shle0
    ax-mp
    notbii
    3bitr2ri
    @4
    @6
    vx
    cA
    @3
    @2
    c0v
    @2
    elch0
    necon3bbii
    rexbii
    3bitri
end
