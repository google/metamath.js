include "cxrn.mm"
include "ccnv.mm"
include "cec.mm"
include "wcel.mm"
include "wbr.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "w3a.mm"
include "wex.mm"
include "wrel.mm"
include "wb.mm"
include "relcnv.mm"
include "relelec.mm"
include "ax-mp.mm"
include "br1cnvxrn2.mm"
include "syl5bb.mm"

theorem elec1cnvxrn2
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
  assert |- ( B e. V -> ( B e. [ A ] `' ( R |X. S ) <-> E. y E. z ( A = <. y , z >. /\ B R y /\ B S z ) ) )

  proof
    cB
    cA
    cR
    cS
    cxrn
    #
    ccnv
    #
    cec
    wcel
    #
    cA
    cB
    @1
    wbr
    #
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
    @4
    cR
    wbr
    cB
    @5
    cS
    wbr
    w3a
    vz
    wex
    vy
    wex
    @1
    wrel
    @2
    @3
    wb
    @0
    relcnv
    cB
    cA
    @1
    relelec
    ax-mp
    vy
    vz
    cA
    cB
    cR
    cS
    cV
    br1cnvxrn2
    syl5bb
end
