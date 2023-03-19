include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "covol.mm"
include "cres.mm"
include "volres.mm"
include "fveq1i.mm"
include "fvres.mm"
include "syl5eq.mm"

theorem mblvol
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( A e. dom vol -> ( vol ` A ) = ( vol* ` A ) )

  proof
    cA
    cvol
    cdm
    #
    wcel
    cA
    cvol
    cfv
    cA
    covol
    @0
    cres
    #
    cfv
    cA
    covol
    cfv
    cA
    cvol
    @1
    volres
    fveq1i
    cA
    @0
    covol
    fvres
    syl5eq
end
