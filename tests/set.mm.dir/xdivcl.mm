include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "xdivcld.mm"

theorem xdivcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR /\ B =/= 0 ) -> ( A /e B ) e. RR* )

  proof
    cA
    cxr
    wcel
    #
    cB
    cr
    wcel
    #
    cB
    cc0
    wne
    #
    w3a
    cA
    cB
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    xdivcld
end
