include "wcel.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "wne.mm"
include "inelcm.mm"
include "expcom.mm"
include "necon2bd.mm"
include "imp.mm"

theorem minel
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. B /\ ( C i^i B ) = (/) ) -> -. A e. C )

  proof
    cA
    cB
    wcel
    #
    cC
    cB
    cin
    #
    c0
    wceq
    cA
    cC
    wcel
    #
    wn
    @0
    @2
    @1
    c0
    @2
    @0
    @1
    c0
    wne
    cA
    cC
    cB
    inelcm
    expcom
    necon2bd
    imp
end
