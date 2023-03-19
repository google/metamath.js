include "com.mm"
include "wss.mm"
include "c0.mm"
include "wcel.mm"
include "cv.mm"
include "csuc.mm"
include "wral.mm"
include "simp1i.mm"
include "wi.mm"
include "wa.mm"
include "w3a.mm"
include "3simpc.mm"
include "ax-mp.mm"
include "wal.mm"
include "df-ral.mm"
include "alral.mm"
include "sylbi.mm"
include "anim2i.mm"
include "peano5.mm"
include "eqssi.mm"

theorem find
  let vx: setvar x
  let cA: class A
  assume find.1: |- ( A C_ _om /\ (/) e. A /\ A. x e. A suc x e. A )

  disjoint A x
  assert |- A = _om

  proof
    cA
    com
    cA
    com
    wss
    #
    c0
    cA
    wcel
    #
    vx
    cv
    #
    csuc
    cA
    wcel
    #
    vx
    cA
    wral
    #
    find.1
    simp1i
    @1
    @2
    cA
    wcel
    @3
    wi
    #
    vx
    com
    wral
    #
    wa
    #
    com
    cA
    wss
    @1
    @4
    wa
    #
    @7
    @0
    @1
    @4
    w3a
    @8
    find.1
    @0
    @1
    @4
    3simpc
    ax-mp
    @4
    @6
    @1
    @4
    @5
    vx
    wal
    @6
    @3
    vx
    cA
    df-ral
    @5
    vx
    com
    alral
    sylbi
    anim2i
    ax-mp
    vx
    cA
    peano5
    ax-mp
    eqssi
end
