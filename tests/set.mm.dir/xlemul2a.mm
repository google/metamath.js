include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "cxmu.mm"
include "co.mm"
include "xlemul1a.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl3l.mm"
include "xmulcom.mm"
include "syl2anc.mm"
include "simpl2.mm"
include "3brtr3d.mm"

theorem xlemul2a
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. RR* /\ B e. RR* /\ ( C e. RR* /\ 0 <_ C ) ) /\ A <_ B ) -> ( C *e A ) <_ ( C *e B ) )

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
    cc0
    cC
    cle
    wbr
    #
    wa
    #
    w3a
    cA
    cB
    cle
    wbr
    #
    wa
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
    cA
    cB
    cC
    xlemul1a
    @6
    @0
    @2
    @7
    @9
    wceq
    @0
    @1
    @4
    @5
    simpl1
    @2
    @3
    @0
    @1
    @5
    simpl3l
    #
    cA
    cC
    xmulcom
    syl2anc
    @6
    @1
    @2
    @8
    @10
    wceq
    @0
    @1
    @4
    @5
    simpl2
    @11
    cB
    cC
    xmulcom
    syl2anc
    3brtr3d
end
