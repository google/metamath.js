include "cgru.mm"
include "wcel.mm"
include "wral.mm"
include "w3a.mm"
include "ciun.mm"
include "cmap.mm"
include "co.mm"
include "cixp.mm"
include "wss.mm"
include "simp1.mm"
include "gruiun.mm"
include "simp2.mm"
include "grumap.mm"
include "syl3anc.mm"
include "ixpssmapg.mm"
include "3ad2ant3.mm"
include "gruss.mm"

theorem gruixp
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cU: class U
  let vy: setvar y
  let cF: class F

  disjoint U x
  disjoint A x
  disjoint U y
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint F x
  disjoint F y
  assert |- ( ( U e. Univ /\ A e. U /\ A. x e. A B e. U ) -> X_ x e. A B e. U )

  proof
    cU
    cgru
    wcel
    #
    cA
    cU
    wcel
    #
    cB
    cU
    wcel
    vx
    cA
    wral
    #
    w3a
    #
    @0
    vx
    cA
    cB
    ciun
    #
    cA
    cmap
    co
    #
    cU
    wcel
    #
    vx
    cA
    cB
    cixp
    #
    @5
    wss
    #
    @7
    cU
    wcel
    @0
    @1
    @2
    simp1
    #
    @3
    @0
    @4
    cU
    wcel
    @1
    @6
    @9
    vx
    cA
    cB
    cU
    gruiun
    @0
    @1
    @2
    simp2
    @4
    cA
    cU
    grumap
    syl3anc
    @2
    @0
    @8
    @1
    vx
    cA
    cB
    cU
    ixpssmapg
    3ad2ant3
    @5
    @7
    cU
    gruss
    syl3anc
end
