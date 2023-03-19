include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cxdiv.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cxmu.mm"
include "crio.mm"
include "xdivval.mm"
include "3expb.mm"
include "3adant2.mm"
include "eqeq1d.mm"
include "wreu.mm"
include "wb.mm"
include "simp2.mm"
include "xreceu.mm"
include "oveq2.mm"
include "riota2.mm"
include "syl2anc.mm"
include "bitr4d.mm"

theorem xdivmul
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( ( A e. RR* /\ B e. RR* /\ ( C e. RR /\ C =/= 0 ) ) -> ( ( A /e C ) = B <-> ( C *e B ) = A ) )

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
    cC
    cc0
    wne
    #
    wa
    #
    w3a
    #
    cA
    cC
    cxdiv
    co
    #
    cB
    wceq
    cC
    vx
    cv
    #
    cxmu
    co
    #
    cA
    wceq
    #
    vx
    cxr
    crio
    #
    cB
    wceq
    #
    cC
    cB
    cxmu
    co
    #
    cA
    wceq
    #
    @5
    @6
    @10
    cB
    @0
    @4
    @6
    @10
    wceq
    #
    @1
    @0
    @2
    @3
    @14
    vx
    cA
    cC
    xdivval
    3expb
    3adant2
    eqeq1d
    @5
    @1
    @9
    vx
    cxr
    wreu
    #
    @13
    @11
    wb
    @0
    @1
    @4
    simp2
    @0
    @4
    @15
    @1
    @0
    @2
    @3
    @15
    vx
    cA
    cC
    xreceu
    3expb
    3adant2
    @9
    @13
    vx
    cxr
    cB
    @7
    cB
    wceq
    @8
    @12
    cA
    @7
    cB
    cC
    cxmu
    oveq2
    eqeq1d
    riota2
    syl2anc
    bitr4d
end
