include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "wceq.mm"
include "wa.mm"
include "letri.mm"
include "letri3i.mm"
include "biimpri.mm"
include "sylan2.mm"
include "3impb.mm"
include "3comr.mm"
include "eqcomd.mm"
include "stoic3.mm"
include "3jca.mm"
include "eqlei.mm"
include "3anim123i.mm"
include "impbii.mm"

theorem le2tri3i
  let cA: class A
  let cB: class B
  let cC: class C
  assume lt.1: |- A e. RR
  assume lt.2: |- B e. RR
  assume lt.3: |- C e. RR


  assert |- ( ( A <_ B /\ B <_ C /\ C <_ A ) <-> ( A = B /\ B = C /\ C = A ) )

  proof
    cA
    cB
    cle
    wbr
    #
    cB
    cC
    cle
    wbr
    #
    cC
    cA
    cle
    wbr
    #
    w3a
    #
    cA
    cB
    wceq
    #
    cB
    cC
    wceq
    #
    cC
    cA
    wceq
    #
    w3a
    @3
    @4
    @5
    @6
    @0
    @1
    @2
    @4
    @1
    @2
    wa
    @0
    cB
    cA
    cle
    wbr
    #
    @4
    cB
    cC
    cA
    lt.2
    lt.3
    lt.1
    letri
    @4
    @0
    @7
    wa
    cA
    cB
    lt.1
    lt.2
    letri3i
    biimpri
    sylan2
    3impb
    @1
    @2
    @0
    @5
    @1
    @2
    @0
    @5
    @2
    @0
    wa
    @1
    cC
    cB
    cle
    wbr
    #
    @5
    cC
    cA
    cB
    lt.3
    lt.1
    lt.2
    letri
    @5
    @1
    @8
    wa
    cB
    cC
    lt.2
    lt.3
    letri3i
    biimpri
    sylan2
    3impb
    3comr
    @0
    @1
    cA
    cC
    cle
    wbr
    #
    @2
    @6
    cA
    cB
    cC
    lt.1
    lt.2
    lt.3
    letri
    @9
    @2
    wa
    #
    cA
    cC
    cA
    cC
    wceq
    @10
    cA
    cC
    lt.1
    lt.3
    letri3i
    biimpri
    eqcomd
    stoic3
    3jca
    @4
    @0
    @5
    @1
    @6
    @2
    cA
    cB
    lt.1
    eqlei
    cB
    cC
    lt.2
    eqlei
    cC
    cA
    lt.3
    eqlei
    3anim123i
    impbii
end
