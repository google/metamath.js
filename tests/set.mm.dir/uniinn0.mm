include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "cuni.mm"
include "wn.mm"
include "wral.mm"
include "wceq.mm"
include "nne.mm"
include "ralbii.mm"
include "ralnex.mm"
include "cvv.mm"
include "cdif.mm"
include "wss.mm"
include "unissb.mm"
include "disj2.mm"
include "3bitr4ri.mm"
include "3bitr3i.mm"
include "necon1abii.mm"

theorem uniinn0
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( U. A i^i B ) =/= (/) <-> E. x e. A ( x i^i B ) =/= (/) )

  proof
    vx
    cv
    #
    cB
    cin
    #
    c0
    wne
    #
    vx
    cA
    wrex
    #
    cA
    cuni
    #
    cB
    cin
    #
    c0
    @2
    wn
    #
    vx
    cA
    wral
    @1
    c0
    wceq
    #
    vx
    cA
    wral
    #
    @3
    wn
    @5
    c0
    wceq
    #
    @6
    @7
    vx
    cA
    @1
    c0
    nne
    ralbii
    @2
    vx
    cA
    ralnex
    @4
    cvv
    cB
    cdif
    #
    wss
    @0
    @10
    wss
    #
    vx
    cA
    wral
    @9
    @8
    vx
    cA
    @10
    unissb
    @4
    cB
    disj2
    @7
    @11
    vx
    cA
    @0
    cB
    disj2
    ralbii
    3bitr4ri
    3bitr3i
    necon1abii
end
