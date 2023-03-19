include "cxrn.mm"
include "ccnv.mm"
include "wbr.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "w3a.mm"
include "wex.mm"
include "xrnrel.mm"
include "relbrcnv.mm"
include "brxrn2.mm"
include "syl5bb.mm"

theorem br1cnvxrn2
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cV: class V

  disjoint A y
  disjoint A z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint R y
  disjoint R z
  disjoint S y
  disjoint S z
  disjoint V y
  disjoint V z
  assert |- ( B e. V -> ( A `' ( R |X. S ) B <-> E. y E. z ( A = <. y , z >. /\ B R y /\ B S z ) ) )

  proof
    cA
    cB
    cR
    cS
    cxrn
    #
    ccnv
    wbr
    cB
    cA
    @0
    wbr
    cB
    cV
    wcel
    cA
    vy
    cv
    #
    vz
    cv
    #
    cop
    wceq
    cB
    @1
    cR
    wbr
    cB
    @2
    cS
    wbr
    w3a
    vz
    wex
    vy
    wex
    cA
    cB
    @0
    cR
    cS
    xrnrel
    relbrcnv
    vy
    vz
    cB
    cA
    cR
    cS
    cV
    brxrn2
    syl5bb
end
