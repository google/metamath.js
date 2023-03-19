include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cfl.mm"
include "cfv.mm"
include "cz.mm"
include "cuz.mm"
include "simp1.mm"
include "flcld.mm"
include "simp2.mm"
include "flwordi.mm"
include "eluz2.mm"
include "syl3anbrc.mm"

theorem flword2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR /\ A <_ B ) -> ( |_ ` B ) e. ( ZZ>= ` ( |_ ` A ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    w3a
    #
    cA
    cfl
    cfv
    #
    cz
    wcel
    cB
    cfl
    cfv
    #
    cz
    wcel
    @4
    @5
    cle
    wbr
    @5
    @4
    cuz
    cfv
    wcel
    @3
    cA
    @0
    @1
    @2
    simp1
    flcld
    @3
    cB
    @0
    @1
    @2
    simp2
    flcld
    cA
    cB
    flwordi
    @4
    @5
    eluz2
    syl3anbrc
end
