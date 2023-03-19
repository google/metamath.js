include "cch.mm"
include "wcel.mm"
include "c0h.mm"
include "wne.mm"
include "cv.mm"
include "wss.mm"
include "cat.mm"
include "wrex.mm"
include "wi.mm"
include "cif.mm"
include "wceq.mm"
include "neeq1.mm"
include "sseq2.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "h0elch.mm"
include "elimel.mm"
include "hatomici.mm"
include "dedth.mm"
include "imp.mm"

theorem hatomic
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( ( A e. CH /\ A =/= 0H ) -> E. x e. HAtoms x C_ A )

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
    #
    cA
    wss
    #
    vx
    cat
    wrex
    #
    @0
    @1
    @4
    wi
    @0
    cA
    c0h
    cif
    #
    c0h
    wne
    #
    @2
    @5
    wss
    #
    vx
    cat
    wrex
    #
    wi
    cA
    c0h
    cA
    @5
    wceq
    #
    @1
    @6
    @4
    @8
    cA
    @5
    c0h
    neeq1
    @9
    @3
    @7
    vx
    cat
    cA
    @5
    @2
    sseq2
    rexbidv
    imbi12d
    vx
    @5
    cA
    c0h
    cch
    h0elch
    elimel
    hatomici
    dedth
    imp
end
