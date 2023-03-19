include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "cin.mm"
include "wceq.mm"
include "zfregs.mm"
include "incom.mm"
include "eqeq1i.mm"
include "rexbii.mm"
include "sylib.mm"
include "disj1.mm"
include "alinexa.mm"
include "dfrex2.mm"
include "notnotb.mm"
include "ralbii.mm"
include "sylnibr.mm"

theorem zfregs2
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( A =/= (/) -> -. A. x e. A E. y ( y e. A /\ y e. x ) )

  proof
    cA
    c0
    wne
    #
    vy
    cv
    #
    cA
    wcel
    #
    @1
    vx
    cv
    #
    wcel
    #
    wa
    vy
    wex
    #
    wn
    #
    wn
    #
    vx
    cA
    wral
    #
    @5
    vx
    cA
    wral
    @0
    @6
    vx
    cA
    wrex
    #
    @8
    wn
    @0
    @2
    @4
    wn
    wi
    vy
    wal
    #
    vx
    cA
    wrex
    #
    @9
    @0
    cA
    @3
    cin
    #
    c0
    wceq
    #
    vx
    cA
    wrex
    #
    @11
    @0
    @3
    cA
    cin
    #
    c0
    wceq
    #
    vx
    cA
    wrex
    @14
    vx
    cA
    zfregs
    @16
    @13
    vx
    cA
    @15
    @12
    c0
    @3
    cA
    incom
    eqeq1i
    rexbii
    sylib
    @13
    @10
    vx
    cA
    vy
    cA
    @3
    disj1
    rexbii
    sylib
    @10
    @6
    vx
    cA
    @2
    @4
    vy
    alinexa
    rexbii
    sylib
    @6
    vx
    cA
    dfrex2
    sylib
    @5
    @7
    vx
    cA
    @5
    notnotb
    ralbii
    sylnibr
end
