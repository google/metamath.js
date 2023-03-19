include "wcel.mm"
include "cxrn.mm"
include "cec.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "copab.mm"
include "cop.mm"
include "wceq.mm"
include "wex.mm"
include "w3a.mm"
include "elecxrn.mm"
include "3anass.mm"
include "2exbii.mm"
include "syl6bb.mm"
include "elopab.mm"
include "syl6bbr.mm"
include "eqrdv.mm"

theorem ecxrn
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  let cS: class S
  let cV: class V
  let vx: setvar x

  disjoint A y
  disjoint A z
  disjoint y z
  disjoint R y
  disjoint R z
  disjoint S y
  disjoint S z
  disjoint V y
  disjoint V z
  disjoint A x
  disjoint x y
  disjoint x z
  disjoint R x
  disjoint S x
  disjoint V x
  assert |- ( A e. V -> [ A ] ( R |X. S ) = { <. y , z >. | ( A R y /\ A S z ) } )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    cR
    cS
    cxrn
    cec
    #
    cA
    vy
    cv
    #
    cR
    wbr
    #
    cA
    vz
    cv
    #
    cS
    wbr
    #
    wa
    #
    vy
    vz
    copab
    #
    @0
    vx
    cv
    #
    @1
    wcel
    #
    @8
    @2
    @4
    cop
    wceq
    #
    @6
    wa
    #
    vz
    wex
    vy
    wex
    #
    @8
    @7
    wcel
    @0
    @9
    @10
    @3
    @5
    w3a
    #
    vz
    wex
    vy
    wex
    @12
    vy
    vz
    cA
    @8
    cR
    cS
    cV
    elecxrn
    @13
    @11
    vy
    vz
    @10
    @3
    @5
    3anass
    2exbii
    syl6bb
    @6
    vy
    vz
    @8
    elopab
    syl6bbr
    eqrdv
end
