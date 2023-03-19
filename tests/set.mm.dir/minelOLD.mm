include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "inelcm.mm"
include "necon2bi.mm"
include "imnan.mm"
include "sylibr.mm"
include "con2d.mm"
include "impcom.mm"

theorem minelOLD
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. B /\ ( C i^i B ) = (/) ) -> -. A e. C )

  proof
    cC
    cB
    cin
    #
    c0
    wceq
    #
    cA
    cB
    wcel
    #
    cA
    cC
    wcel
    #
    wn
    @1
    @3
    @2
    @1
    @3
    @2
    wa
    #
    wn
    @3
    @2
    wn
    wi
    @4
    @0
    c0
    cA
    cC
    cB
    inelcm
    necon2bi
    @3
    @2
    imnan
    sylibr
    con2d
    impcom
end
