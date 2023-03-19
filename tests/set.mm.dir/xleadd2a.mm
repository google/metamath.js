include "cxr.mm"
include "wcel.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cxad.mm"
include "co.mm"
include "xleadd1a.mm"
include "wceq.mm"
include "xaddcom.mm"
include "3adant2.mm"
include "adantr.mm"
include "3adant1.mm"
include "3brtr3d.mm"

theorem xleadd2a
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) /\ A <_ B ) -> ( C +e A ) <_ ( C +e B ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cC
    cxr
    wcel
    #
    w3a
    #
    cA
    cB
    cle
    wbr
    #
    wa
    cA
    cC
    cxad
    co
    #
    cB
    cC
    cxad
    co
    #
    cC
    cA
    cxad
    co
    #
    cC
    cB
    cxad
    co
    #
    cle
    cA
    cB
    cC
    xleadd1a
    @3
    @5
    @7
    wceq
    #
    @4
    @0
    @2
    @9
    @1
    cA
    cC
    xaddcom
    3adant2
    adantr
    @3
    @6
    @8
    wceq
    #
    @4
    @1
    @2
    @10
    @0
    cB
    cC
    xaddcom
    3adant1
    adantr
    3brtr3d
end
