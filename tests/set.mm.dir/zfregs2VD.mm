include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wral.mm"
include "wn.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "cin.mm"
include "wceq.mm"
include "idn1.mm"
include "zfregs.mm"
include "e1a.mm"
include "incom.mm"
include "eqeq1i.mm"
include "rexbii.mm"
include "e1bi.mm"
include "disj1.mm"
include "alinexa.mm"
include "dfrex2.mm"
include "notnotr.mm"
include "notnot.mm"
include "impbii.mm"
include "ralbii.mm"
include "notbii.mm"
include "in1.mm"

theorem zfregs2VD
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
    vx
    cA
    wral
    #
    wn
    #
    @0
    @5
    wn
    #
    wn
    #
    vx
    cA
    wral
    #
    wn
    #
    @7
    @0
    @8
    vx
    cA
    wrex
    #
    @11
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
    @12
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
    @14
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
    #
    @17
    @0
    @0
    @20
    @0
    idn1
    vx
    cA
    zfregs
    e1a
    @19
    @16
    vx
    cA
    @18
    @15
    c0
    @3
    cA
    incom
    eqeq1i
    rexbii
    e1bi
    @16
    @13
    vx
    cA
    vy
    cA
    @3
    disj1
    rexbii
    e1bi
    @13
    @8
    vx
    cA
    @2
    @4
    vy
    alinexa
    rexbii
    e1bi
    @8
    vx
    cA
    dfrex2
    e1bi
    @10
    @6
    @9
    @5
    vx
    cA
    @9
    @5
    @5
    notnotr
    @5
    notnot
    impbii
    ralbii
    notbii
    e1bi
    in1
end
