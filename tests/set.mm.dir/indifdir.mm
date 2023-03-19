include "cdif.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "pm3.24.mm"
include "intnan.mm"
include "anass.mm"
include "mtbir.mm"
include "biorfi.mm"
include "an32.mm"
include "andi.mm"
include "3bitr4i.mm"
include "ianor.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "elin.mm"
include "eldif.mm"
include "anbi1i.mm"
include "bitri.mm"
include "notbii.mm"
include "anbi12i.mm"
include "eqriv.mm"

theorem indifdir
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( ( A \ B ) i^i C ) = ( ( A i^i C ) \ ( B i^i C ) )

  proof
    vx
    cA
    cB
    cdif
    #
    cC
    cin
    #
    cA
    cC
    cin
    #
    cB
    cC
    cin
    #
    cdif
    #
    vx
    cv
    #
    cA
    wcel
    #
    @5
    cB
    wcel
    #
    wn
    #
    wa
    #
    @5
    cC
    wcel
    #
    wa
    #
    @6
    @10
    wa
    #
    @7
    @10
    wa
    #
    wn
    #
    wa
    #
    @5
    @1
    wcel
    #
    @5
    @4
    wcel
    #
    @11
    @12
    @8
    @10
    wn
    #
    wo
    #
    wa
    #
    @15
    @12
    @8
    wa
    #
    @21
    @12
    @18
    wa
    #
    wo
    @11
    @20
    @22
    @21
    @22
    @6
    @10
    @18
    wa
    #
    wa
    @23
    @6
    @10
    pm3.24
    intnan
    @6
    @10
    @18
    anass
    mtbir
    biorfi
    @6
    @8
    @10
    an32
    @12
    @8
    @18
    andi
    3bitr4i
    @14
    @19
    @12
    @7
    @10
    ianor
    anbi2i
    bitr4i
    @16
    @5
    @0
    wcel
    #
    @10
    wa
    @11
    @5
    @0
    cC
    elin
    @24
    @9
    @10
    @5
    cA
    cB
    eldif
    anbi1i
    bitri
    @17
    @5
    @2
    wcel
    #
    @5
    @3
    wcel
    #
    wn
    #
    wa
    @15
    @5
    @2
    @3
    eldif
    @25
    @12
    @27
    @14
    @5
    cA
    cC
    elin
    @26
    @13
    @5
    cB
    cC
    elin
    notbii
    anbi12i
    bitri
    3bitr4i
    eqriv
end
