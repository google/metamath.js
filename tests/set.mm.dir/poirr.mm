include "wcel.mm"
include "wpo.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "df-3an.mm"
include "anabs1.mm"
include "anidm.mm"
include "3bitrri.mm"
include "wi.mm"
include "pocl.mm"
include "imp.mm"
include "simpld.mm"
include "sylan2b.mm"

theorem poirr
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( ( R Po A /\ B e. A ) -> -. B R B )

  proof
    cB
    cA
    wcel
    #
    cA
    cR
    wpo
    #
    @0
    @0
    @0
    w3a
    #
    cB
    cB
    cR
    wbr
    #
    wn
    #
    @2
    @0
    @0
    wa
    #
    @0
    wa
    @5
    @0
    @0
    @0
    @0
    df-3an
    @0
    @0
    anabs1
    @0
    anidm
    3bitrri
    @1
    @2
    wa
    @4
    @3
    @3
    wa
    @3
    wi
    #
    @1
    @2
    @4
    @6
    wa
    cA
    cB
    cB
    cB
    cR
    pocl
    imp
    simpld
    sylan2b
end
