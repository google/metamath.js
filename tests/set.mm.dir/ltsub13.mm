include "cr.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "wb.mm"
include "w3a.mm"
include "caddc.mm"
include "ltaddsub.mm"
include "ltaddsub2.mm"
include "bitr3d.mm"
include "3com23.mm"

theorem ltsub13
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( A < ( B - C ) <-> C < ( B - A ) ) )

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
    clt
    wbr
    #
    cC
    cB
    cA
    cmin
    co
    clt
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
    clt
    wbr
    @3
    @4
    cA
    cC
    cB
    ltaddsub
    cA
    cC
    cB
    ltaddsub2
    bitr3d
    3com23
end
