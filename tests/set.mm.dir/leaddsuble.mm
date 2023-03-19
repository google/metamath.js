include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "wb.mm"
include "leadd2.mm"
include "3comr.mm"
include "readdcl.mm"
include "3adant3.mm"
include "simp3.mm"
include "simp1.mm"
include "lesubaddd.mm"
include "bitr4d.mm"

theorem leaddsuble
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( B <_ C <-> ( ( A + B ) - C ) <_ A ) )

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
    #
    cB
    cC
    cle
    wbr
    #
    cA
    cB
    caddc
    co
    #
    cA
    cC
    caddc
    co
    cle
    wbr
    #
    @5
    cC
    cmin
    co
    cA
    cle
    wbr
    @1
    @2
    @0
    @4
    @6
    wb
    cB
    cC
    cA
    leadd2
    3comr
    @3
    @5
    cC
    cA
    @0
    @1
    @5
    cr
    wcel
    @2
    cA
    cB
    readdcl
    3adant3
    @0
    @1
    @2
    simp3
    @0
    @1
    @2
    simp1
    lesubaddd
    bitr4d
end
