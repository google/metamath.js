include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3l.mm"
include "simp3r.mm"
include "mulcan2d.mm"

theorem mulcan2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ ( C e. CC /\ C =/= 0 ) ) -> ( ( A x. C ) = ( B x. C ) <-> A = B ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    cC
    cc0
    wne
    #
    wa
    #
    w3a
    cA
    cB
    cC
    @0
    @1
    @4
    simp1
    @0
    @1
    @4
    simp2
    @0
    @1
    @2
    @3
    simp3l
    @0
    @1
    @2
    @3
    simp3r
    mulcan2d
end
