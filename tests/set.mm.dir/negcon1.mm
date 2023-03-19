include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "wceq.mm"
include "wb.mm"
include "negcl.mm"
include "neg11.mm"
include "sylan.mm"
include "negneg.mm"
include "adantr.mm"
include "eqeq1d.mm"
include "bitr3d.mm"
include "eqcom.mm"
include "syl6bb.mm"

theorem negcon1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( -u A = B <-> -u B = A ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    cneg
    #
    cB
    wceq
    #
    cA
    cB
    cneg
    #
    wceq
    #
    @5
    cA
    wceq
    @2
    @3
    cneg
    #
    @5
    wceq
    #
    @4
    @6
    @0
    @3
    cc
    wcel
    @1
    @8
    @4
    wb
    cA
    negcl
    @3
    cB
    neg11
    sylan
    @2
    @7
    cA
    @5
    @0
    @7
    cA
    wceq
    @1
    cA
    negneg
    adantr
    eqeq1d
    bitr3d
    cA
    @5
    eqcom
    syl6bb
end
