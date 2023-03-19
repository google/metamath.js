include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "w3a.mm"
include "cxad.mm"
include "co.mm"
include "cxmu.mm"
include "wceq.mm"
include "xadddi.mm"
include "3coml.mm"
include "xaddcl.mm"
include "3adant3.mm"
include "rexr.mm"
include "3ad2ant3.mm"
include "xmulcom.mm"
include "syl2anc.mm"
include "simp1.mm"
include "simp2.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"

theorem xadddir
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR* /\ B e. RR* /\ C e. RR ) -> ( ( A +e B ) *e C ) = ( ( A *e C ) +e ( B *e C ) ) )

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
    cr
    wcel
    #
    w3a
    #
    cC
    cA
    cB
    cxad
    co
    #
    cxmu
    co
    #
    cC
    cA
    cxmu
    co
    #
    cC
    cB
    cxmu
    co
    #
    cxad
    co
    #
    @4
    cC
    cxmu
    co
    #
    cA
    cC
    cxmu
    co
    #
    cB
    cC
    cxmu
    co
    #
    cxad
    co
    @2
    @0
    @1
    @5
    @8
    wceq
    cC
    cA
    cB
    xadddi
    3coml
    @3
    @4
    cxr
    wcel
    #
    cC
    cxr
    wcel
    #
    @9
    @5
    wceq
    @0
    @1
    @12
    @2
    cA
    cB
    xaddcl
    3adant3
    @2
    @0
    @13
    @1
    cC
    rexr
    3ad2ant3
    #
    @4
    cC
    xmulcom
    syl2anc
    @3
    @10
    @6
    @11
    @7
    cxad
    @3
    @0
    @13
    @10
    @6
    wceq
    @0
    @1
    @2
    simp1
    @14
    cA
    cC
    xmulcom
    syl2anc
    @3
    @1
    @13
    @11
    @7
    wceq
    @0
    @1
    @2
    simp2
    @14
    cB
    cC
    xmulcom
    syl2anc
    oveq12d
    3eqtr4d
end
