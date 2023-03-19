include "cch.mm"
include "wcel.mm"
include "c0h.mm"
include "wne.mm"
include "cv.mm"
include "c0v.mm"
include "wrex.mm"
include "wb.mm"
include "cif.mm"
include "wceq.mm"
include "neeq1.mm"
include "rexeq.mm"
include "bibi12d.mm"
include "h0elch.mm"
include "elimel.mm"
include "chne0i.mm"
include "dedth.mm"

theorem chne0
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. CH -> ( A =/= 0H <-> E. x e. A x =/= 0h ) )

  proof
    cA
    cch
    wcel
    #
    cA
    c0h
    wne
    #
    vx
    cv
    c0v
    wne
    #
    vx
    cA
    wrex
    #
    wb
    @0
    cA
    c0h
    cif
    #
    c0h
    wne
    #
    @2
    vx
    @4
    wrex
    #
    wb
    cA
    c0h
    cA
    @4
    wceq
    @1
    @5
    @3
    @6
    cA
    @4
    c0h
    neeq1
    @2
    vx
    cA
    @4
    rexeq
    bibi12d
    vx
    @4
    cA
    c0h
    cch
    h0elch
    elimel
    chne0i
    dedth
end
