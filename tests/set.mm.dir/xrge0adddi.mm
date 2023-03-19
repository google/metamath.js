include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "w3a.mm"
include "cxad.mm"
include "cxmu.mm"
include "xrge0adddir.mm"
include "cxr.mm"
include "wceq.mm"
include "iccssxr.mm"
include "simp1.mm"
include "sseldi.mm"
include "simp2.mm"
include "xaddcld.mm"
include "simp3.mm"
include "xmulcom.mm"
include "syl2anc.mm"
include "oveq12d.mm"
include "3eqtr3d.mm"

theorem xrge0adddi
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ( 0 [,] +oo ) /\ B e. ( 0 [,] +oo ) /\ C e. ( 0 [,] +oo ) ) -> ( C *e ( A +e B ) ) = ( ( C *e A ) +e ( C *e B ) ) )

  proof
    cA
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cC
    @0
    wcel
    #
    w3a
    #
    cA
    cB
    cxad
    co
    #
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
    cC
    @5
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
    cA
    cB
    cC
    xrge0adddir
    @4
    @5
    cxr
    wcel
    cC
    cxr
    wcel
    #
    @6
    @9
    wceq
    @4
    cA
    cB
    @4
    @0
    cxr
    cA
    cc0
    cpnf
    iccssxr
    #
    @1
    @2
    @3
    simp1
    sseldi
    #
    @4
    @0
    cxr
    cB
    @13
    @1
    @2
    @3
    simp2
    sseldi
    #
    xaddcld
    @4
    @0
    cxr
    cC
    @13
    @1
    @2
    @3
    simp3
    sseldi
    #
    @5
    cC
    xmulcom
    syl2anc
    @4
    @7
    @10
    @8
    @11
    cxad
    @4
    cA
    cxr
    wcel
    @12
    @7
    @10
    wceq
    @14
    @16
    cA
    cC
    xmulcom
    syl2anc
    @4
    cB
    cxr
    wcel
    @12
    @8
    @11
    wceq
    @15
    @16
    cB
    cC
    xmulcom
    syl2anc
    oveq12d
    3eqtr3d
end
