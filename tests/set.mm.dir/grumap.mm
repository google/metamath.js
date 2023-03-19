include "cgru.mm"
include "wcel.mm"
include "w3a.mm"
include "cxp.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wss.mm"
include "simp1.mm"
include "gruxp.mm"
include "3com23.mm"
include "grupw.mm"
include "syl2anc.mm"
include "mapsspw.mm"
include "a1i.mm"
include "gruss.mm"
include "syl3anc.mm"

theorem grumap
  let cA: class A
  let cB: class B
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let cF: class F


  assert |- ( ( U e. Univ /\ A e. U /\ B e. U ) -> ( A ^m B ) e. U )

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
    #
    w3a
    #
    @0
    cB
    cA
    cxp
    #
    cpw
    #
    cU
    wcel
    #
    cA
    cB
    cmap
    co
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
    #
    @6
    @9
    @0
    @2
    @1
    @10
    cB
    cA
    cU
    gruxp
    3com23
    @4
    cU
    grupw
    syl2anc
    @8
    @3
    cA
    cB
    mapsspw
    a1i
    @5
    @7
    cU
    gruss
    syl3anc
end
