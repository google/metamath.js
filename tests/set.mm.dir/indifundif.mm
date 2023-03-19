include "cin.mm"
include "cdif.mm"
include "cun.mm"
include "difindi.mm"
include "difundir.mm"
include "inundif.mm"
include "difeq1i.mm"
include "uncom.mm"
include "3eqtr3i.mm"
include "uneq2i.mm"
include "unass.mm"
include "undifabs.mm"
include "uneq1i.mm"
include "3eqtr2i.mm"
include "3eqtrri.mm"

theorem indifundif
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A i^i B ) \ C ) u. ( A \ B ) ) = ( A \ ( B i^i C ) )

  proof
    cA
    cB
    cC
    cin
    cdif
    cA
    cB
    cdif
    #
    cA
    cC
    cdif
    #
    cun
    #
    @0
    cA
    cB
    cin
    #
    cC
    cdif
    #
    cun
    #
    @4
    @0
    cun
    cA
    cB
    cC
    difindi
    @2
    @0
    @0
    cC
    cdif
    #
    @4
    cun
    #
    cun
    @0
    @6
    cun
    #
    @4
    cun
    @5
    @1
    @7
    @0
    @3
    @0
    cun
    #
    cC
    cdif
    @4
    @6
    cun
    @1
    @7
    @3
    @0
    cC
    difundir
    @9
    cA
    cC
    cA
    cB
    inundif
    difeq1i
    @4
    @6
    uncom
    3eqtr3i
    uneq2i
    @0
    @6
    @4
    unass
    @8
    @0
    @4
    @0
    cC
    undifabs
    uneq1i
    3eqtr2i
    @0
    @4
    uncom
    3eqtrri
end
