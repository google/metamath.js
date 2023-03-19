include "cioo.mm"
include "co.mm"
include "wcel.mm"
include "cxr.mm"
include "cr.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "eliooxr.mm"
include "elioore.mm"
include "jca.mm"
include "df-3an.mm"
include "sylibr.mm"
include "eliooord.mm"
include "rexr.mm"
include "3anim3i.mm"
include "anim1i.mm"
include "elioo3g.mm"
include "impbii.mm"

theorem elioo4g
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( C e. ( A (,) B ) <-> ( ( A e. RR* /\ B e. RR* /\ C e. RR ) /\ ( A < C /\ C < B ) ) )

  proof
    cC
    cA
    cB
    cioo
    co
    wcel
    #
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cC
    cr
    wcel
    #
    w3a
    #
    cA
    cC
    clt
    wbr
    cC
    cB
    clt
    wbr
    wa
    #
    wa
    #
    @0
    @4
    @5
    @0
    @1
    @2
    wa
    #
    @3
    wa
    @4
    @0
    @7
    @3
    cC
    cA
    cB
    eliooxr
    cC
    cA
    cB
    elioore
    jca
    @1
    @2
    @3
    df-3an
    sylibr
    cC
    cA
    cB
    eliooord
    jca
    @6
    @1
    @2
    cC
    cxr
    wcel
    #
    w3a
    #
    @5
    wa
    @0
    @4
    @9
    @5
    @3
    @8
    @1
    @2
    cC
    rexr
    3anim3i
    anim1i
    cA
    cB
    cC
    elioo3g
    sylibr
    impbii
end
