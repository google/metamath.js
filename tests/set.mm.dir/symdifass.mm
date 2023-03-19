include "csymdif.mm"
include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "wn.mm"
include "biass.mm"
include "notbii.mm"
include "xor3.mm"
include "notbi.mm"
include "bitr4i.mm"
include "con1bii.mm"
include "3bitr3ri.mm"
include "elsymdif.mm"
include "bibi2i.mm"
include "bibi1i.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem symdifass
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A /_\ ( B /_\ C ) ) = ( ( A /_\ B ) /_\ C )

  proof
    vx
    cA
    cB
    cC
    csymdif
    #
    csymdif
    #
    cA
    cB
    csymdif
    #
    cC
    csymdif
    #
    vx
    cv
    #
    cA
    wcel
    #
    @4
    @0
    wcel
    #
    wb
    #
    wn
    @4
    @2
    wcel
    #
    @4
    cC
    wcel
    #
    wb
    #
    wn
    @4
    @1
    wcel
    @4
    @3
    wcel
    @7
    @10
    @5
    @4
    cB
    wcel
    #
    @9
    wb
    #
    wn
    #
    wb
    #
    @5
    @11
    wb
    #
    wn
    #
    @9
    wb
    #
    @7
    @10
    @15
    @9
    wb
    #
    wn
    @5
    @12
    wb
    #
    wn
    @17
    @14
    @18
    @19
    @5
    @11
    @9
    biass
    notbii
    @17
    @18
    @17
    wn
    @16
    @9
    wn
    wb
    @18
    @16
    @9
    xor3
    @15
    @9
    notbi
    bitr4i
    con1bii
    @5
    @12
    xor3
    3bitr3ri
    @6
    @13
    @5
    @4
    cB
    cC
    elsymdif
    bibi2i
    @8
    @16
    @9
    @4
    cA
    cB
    elsymdif
    bibi1i
    3bitr4i
    notbii
    @4
    cA
    @0
    elsymdif
    @4
    @2
    cC
    elsymdif
    3bitr4i
    eqriv
end
