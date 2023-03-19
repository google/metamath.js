include "cr.mm"
include "wcel.mm"
include "cicc.mm"
include "co.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "elicc2.mm"
include "biimp3a.mm"
include "simp1d.mm"

theorem eliccre
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. ( A [,] B ) ) -> C e. RR )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cC
    cA
    cB
    cicc
    co
    wcel
    #
    w3a
    cC
    cr
    wcel
    #
    cA
    cC
    cle
    wbr
    #
    cC
    cB
    cle
    wbr
    #
    @0
    @1
    @2
    @3
    @4
    @5
    w3a
    cA
    cB
    cC
    elicc2
    biimp3a
    simp1d
end
