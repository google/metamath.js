include "cr.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wb.mm"
include "w3a.mm"
include "caddc.mm"
include "leaddsub.mm"
include "leaddsub2.mm"
include "bitr3d.mm"
include "3com23.mm"

theorem lesub
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( A <_ ( B - C ) <-> C <_ ( B - A ) ) )

  proof
    cA
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    cC
    cmin
    co
    cle
    wbr
    #
    cC
    cB
    cA
    cmin
    co
    cle
    wbr
    #
    wb
    @0
    @1
    @2
    w3a
    cA
    cC
    caddc
    co
    cB
    cle
    wbr
    @3
    @4
    cA
    cC
    cB
    leaddsub
    cA
    cC
    cB
    leaddsub2
    bitr3d
    3com23
end
