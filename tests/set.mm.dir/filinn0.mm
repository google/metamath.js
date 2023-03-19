include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "simp1.mm"
include "filin.mm"
include "fileln0.mm"
include "syl2anc.mm"

theorem filinn0
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X


  assert |- ( ( F e. ( Fil ` X ) /\ A e. F /\ B e. F ) -> ( A i^i B ) =/= (/) )

  proof
    cF
    cX
    cfil
    cfv
    wcel
    #
    cA
    cF
    wcel
    #
    cB
    cF
    wcel
    #
    w3a
    @0
    cA
    cB
    cin
    #
    cF
    wcel
    @3
    c0
    wne
    @0
    @1
    @2
    simp1
    cA
    cB
    cF
    cX
    filin
    @3
    cF
    cX
    fileln0
    syl2anc
end
