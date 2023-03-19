include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "cltrr.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "ax-pre-ltadd.mm"
include "wb.mm"
include "ltxrlt.mm"
include "3adant3.mm"
include "wa.mm"
include "readdcl.mm"
include "syl2an.mm"
include "3impdi.mm"
include "3coml.mm"
include "3imtr4d.mm"

theorem axltadd
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( A < B -> ( C + A ) < ( C + B ) ) )

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
    cltrr
    wbr
    #
    cC
    cA
    caddc
    co
    #
    cC
    cB
    caddc
    co
    #
    cltrr
    wbr
    #
    cA
    cB
    clt
    wbr
    #
    @4
    @5
    clt
    wbr
    #
    cA
    cB
    cC
    ax-pre-ltadd
    @0
    @1
    @7
    @3
    wb
    @2
    cA
    cB
    ltxrlt
    3adant3
    @2
    @0
    @1
    @8
    @6
    wb
    #
    @2
    @0
    @1
    @9
    @2
    @0
    wa
    @4
    cr
    wcel
    @5
    cr
    wcel
    @9
    @2
    @1
    wa
    cC
    cA
    readdcl
    cC
    cB
    readdcl
    @4
    @5
    ltxrlt
    syl2an
    3impdi
    3coml
    3imtr4d
end
