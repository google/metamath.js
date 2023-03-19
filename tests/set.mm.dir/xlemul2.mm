include "cxr.mm"
include "wcel.mm"
include "crp.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "cxmu.mm"
include "co.mm"
include "xlemul1.mm"
include "wceq.mm"
include "simp1.mm"
include "rpxr.mm"
include "3ad2ant3.mm"
include "xmulcom.mm"
include "syl2anc.mm"
include "simp2.mm"
include "breq12d.mm"
include "bitrd.mm"

theorem xlemul2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR* /\ B e. RR* /\ C e. RR+ ) -> ( A <_ B <-> ( C *e A ) <_ ( C *e B ) ) )

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
    crp
    wcel
    #
    w3a
    #
    cA
    cB
    cle
    wbr
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
    cle
    wbr
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
    cle
    wbr
    cA
    cB
    cC
    xlemul1
    @3
    @4
    @6
    @5
    @7
    cle
    @3
    @0
    cC
    cxr
    wcel
    #
    @4
    @6
    wceq
    @0
    @1
    @2
    simp1
    @2
    @0
    @8
    @1
    cC
    rpxr
    3ad2ant3
    #
    cA
    cC
    xmulcom
    syl2anc
    @3
    @1
    @8
    @5
    @7
    wceq
    @0
    @1
    @2
    simp2
    @9
    cB
    cC
    xmulcom
    syl2anc
    breq12d
    bitrd
end
