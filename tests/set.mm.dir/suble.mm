include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "lesubadd.mm"
include "wb.mm"
include "lesubadd2.mm"
include "3com23.mm"
include "bitr4d.mm"

theorem suble
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( ( A - B ) <_ C <-> ( A - C ) <_ B ) )

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
    cr
    wcel
    #
    w3a
    cA
    cB
    cmin
    co
    cC
    cle
    wbr
    cA
    cC
    cB
    caddc
    co
    cle
    wbr
    #
    cA
    cC
    cmin
    co
    cB
    cle
    wbr
    #
    cA
    cB
    cC
    lesubadd
    @0
    @2
    @1
    @4
    @3
    wb
    cA
    cC
    cB
    lesubadd2
    3com23
    bitr4d
end
