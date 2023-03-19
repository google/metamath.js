include "wf.mm"
include "cres.mm"
include "ccnv.mm"
include "relcnv.mm"
include "relres.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wa.mm"
include "opelf.mm"
include "simpld.mm"
include "ex.mm"
include "pm4.71d.mm"
include "vex.mm"
include "opelcnv.mm"
include "opelres.mm"
include "bitri.mm"
include "syl6bbr.mm"
include "simprd.mm"
include "anbi1i.mm"
include "bitr3d.mm"
include "eqrelrdv.mm"

theorem fcnvres
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y


  assert |- ( F : A --> B -> `' ( F |` A ) = ( `' F |` B ) )

  proof
    cA
    cB
    cF
    wf
    #
    vy
    vx
    cF
    cA
    cres
    #
    ccnv
    #
    cF
    ccnv
    #
    cB
    cres
    #
    @1
    relcnv
    @3
    cB
    relres
    @0
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cF
    wcel
    #
    @6
    @5
    cop
    #
    @2
    wcel
    #
    @9
    @4
    wcel
    #
    @0
    @8
    @8
    @5
    cA
    wcel
    #
    wa
    #
    @10
    @0
    @8
    @12
    @0
    @8
    @12
    @0
    @8
    wa
    #
    @12
    @6
    cB
    wcel
    #
    cA
    cB
    @5
    @6
    cF
    opelf
    #
    simpld
    ex
    pm4.71d
    @10
    @7
    @1
    wcel
    @13
    @6
    @5
    @1
    vy
    vex
    #
    vx
    vex
    #
    opelcnv
    @5
    @6
    cF
    cA
    @17
    opelres
    bitri
    syl6bbr
    @0
    @8
    @8
    @15
    wa
    #
    @11
    @0
    @8
    @15
    @0
    @8
    @15
    @14
    @12
    @15
    @16
    simprd
    ex
    pm4.71d
    @11
    @9
    @3
    wcel
    #
    @15
    wa
    @19
    @6
    @5
    @3
    cB
    @18
    opelres
    @20
    @8
    @15
    @6
    @5
    cF
    @17
    @18
    opelcnv
    anbi1i
    bitri
    syl6bbr
    bitr3d
    eqrelrdv
end
