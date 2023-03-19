include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "cxad.mm"
include "co.mm"
include "cxmu.mm"
include "wceq.mm"
include "xadddi2.mm"
include "3coml.mm"
include "simp1l.mm"
include "simp2l.mm"
include "xaddcl.mm"
include "syl2anc.mm"
include "simp3.mm"
include "xmulcom.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"

theorem xadddi2r
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. RR* /\ 0 <_ A ) /\ ( B e. RR* /\ 0 <_ B ) /\ C e. RR* ) -> ( ( A +e B ) *e C ) = ( ( A *e C ) +e ( B *e C ) ) )

  proof
    cA
    cxr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    cB
    cxr
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    #
    cC
    cxr
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
    @8
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
    @6
    @2
    @5
    @9
    @12
    wceq
    cC
    cA
    cB
    xadddi2
    3coml
    @7
    @8
    cxr
    wcel
    #
    @6
    @13
    @9
    wceq
    @7
    @0
    @3
    @16
    @0
    @1
    @5
    @6
    simp1l
    #
    @2
    @3
    @4
    @6
    simp2l
    #
    cA
    cB
    xaddcl
    syl2anc
    @2
    @5
    @6
    simp3
    #
    @8
    cC
    xmulcom
    syl2anc
    @7
    @14
    @10
    @15
    @11
    cxad
    @7
    @0
    @6
    @14
    @10
    wceq
    @17
    @19
    cA
    cC
    xmulcom
    syl2anc
    @7
    @3
    @6
    @15
    @11
    wceq
    @18
    @19
    cB
    cC
    xmulcom
    syl2anc
    oveq12d
    3eqtr4d
end
