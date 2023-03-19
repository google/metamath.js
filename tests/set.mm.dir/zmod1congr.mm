include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cmo.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "zmod10.mm"
include "adantr.mm"
include "adantl.mm"
include "eqtr4d.mm"

theorem zmod1congr
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ZZ /\ B e. ZZ ) -> ( A mod 1 ) = ( B mod 1 ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    cA
    c1
    cmo
    co
    #
    cc0
    cB
    c1
    cmo
    co
    #
    @0
    @2
    cc0
    wceq
    @1
    cA
    zmod10
    adantr
    @1
    @3
    cc0
    wceq
    @0
    cB
    zmod10
    adantl
    eqtr4d
end
