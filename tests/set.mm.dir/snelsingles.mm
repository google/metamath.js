include "csn.mm"
include "csingles.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "cvv.mm"
include "isset.mm"
include "eqcom.mm"
include "exbii.mm"
include "bitri.mm"
include "mpbi.mm"
include "sneq.mm"
include "eximii.mm"
include "elsingles.mm"
include "mpbir.mm"

theorem snelsingles
  let cA: class A
  let vx: setvar x
  assume snelsingles.1: |- A e. _V


  assert |- { A } e. Singletons

  proof
    cA
    csn
    #
    csingles
    wcel
    @0
    vx
    cv
    #
    csn
    wceq
    #
    vx
    wex
    cA
    @1
    wceq
    #
    @2
    vx
    cA
    cvv
    wcel
    #
    @3
    vx
    wex
    #
    snelsingles.1
    @4
    @1
    cA
    wceq
    #
    vx
    wex
    @5
    vx
    cA
    isset
    @6
    @3
    vx
    @1
    cA
    eqcom
    exbii
    bitri
    mpbi
    cA
    @1
    sneq
    eximii
    vx
    @0
    elsingles
    mpbir
end
