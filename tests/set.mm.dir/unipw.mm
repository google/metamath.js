include "cpw.mm"
include "cuni.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "eluni.mm"
include "elelpwi.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "csn.mm"
include "vsnid.mm"
include "snelpwi.mm"
include "elunii.mm"
include "sylancr.mm"
include "impbii.mm"
include "eqriv.mm"

theorem unipw
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- U. ~P A = A

  proof
    vx
    cA
    cpw
    #
    cuni
    #
    cA
    vx
    cv
    #
    @1
    wcel
    #
    @2
    cA
    wcel
    #
    @3
    @2
    vy
    cv
    #
    wcel
    @5
    @0
    wcel
    wa
    #
    vy
    wex
    @4
    vy
    @2
    @0
    eluni
    @6
    @4
    vy
    @2
    @5
    cA
    elelpwi
    exlimiv
    sylbi
    @4
    @2
    @2
    csn
    #
    wcel
    @7
    @0
    wcel
    @3
    vx
    vsnid
    @2
    cA
    snelpwi
    @2
    @7
    @0
    elunii
    sylancr
    impbii
    eqriv
end
