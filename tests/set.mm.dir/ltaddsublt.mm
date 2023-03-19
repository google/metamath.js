include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "wb.mm"
include "ltadd2.mm"
include "3comr.mm"
include "readdcl.mm"
include "3adant3.mm"
include "simp3.mm"
include "simp1.mm"
include "ltsubaddd.mm"
include "bitr4d.mm"

theorem ltaddsublt
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( B < C <-> ( ( A + B ) - C ) < A ) )

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
    clt
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
    clt
    wbr
    #
    @5
    cC
    cmin
    co
    cA
    clt
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
    ltadd2
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
    ltsubaddd
    bitr4d
end
