include "cres.mm"
include "ccnv.mm"
include "cima.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "cop.mm"
include "wa.mm"
include "wex.mm"
include "19.41v.mm"
include "vex.mm"
include "opelres.mm"
include "opelcnv.mm"
include "anbi1i.mm"
include "3bitr4i.mm"
include "bianass.mm"
include "exbii.mm"
include "elima3.mm"
include "elin.mm"
include "eqriv.mm"

theorem cnvresima
  let cA: class A
  let cB: class B
  let cF: class F
  let vs: setvar s
  let vt: setvar t


  assert |- ( `' ( F |` A ) " B ) = ( ( `' F " B ) i^i A )

  proof
    vt
    cF
    cA
    cres
    #
    ccnv
    #
    cB
    cima
    #
    cF
    ccnv
    #
    cB
    cima
    #
    cA
    cin
    #
    vs
    cv
    #
    cB
    wcel
    #
    @6
    vt
    cv
    #
    cop
    #
    @1
    wcel
    #
    wa
    #
    vs
    wex
    #
    @8
    @4
    wcel
    #
    @8
    cA
    wcel
    #
    wa
    #
    @8
    @2
    wcel
    @8
    @5
    wcel
    @7
    @9
    @3
    wcel
    #
    wa
    #
    @14
    wa
    #
    vs
    wex
    @17
    vs
    wex
    #
    @14
    wa
    @12
    @15
    @17
    @14
    vs
    19.41v
    @11
    @18
    vs
    @10
    @16
    @14
    @7
    @8
    @6
    cop
    #
    @0
    wcel
    @20
    cF
    wcel
    #
    @14
    wa
    @10
    @16
    @14
    wa
    @8
    @6
    cF
    cA
    vs
    vex
    #
    opelres
    @6
    @8
    @0
    @22
    vt
    vex
    #
    opelcnv
    @16
    @21
    @14
    @6
    @8
    cF
    @22
    @23
    opelcnv
    anbi1i
    3bitr4i
    bianass
    exbii
    @13
    @19
    @14
    vs
    @8
    @3
    cB
    @23
    elima3
    anbi1i
    3bitr4i
    vs
    @8
    @1
    cB
    @23
    elima3
    @8
    @4
    cA
    elin
    3bitr4i
    eqriv
end
