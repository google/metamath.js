include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cismty.mm"
include "co.mm"
include "w3a.mm"
include "cbnd.mm"
include "wi.mm"
include "ismtybndlem.mm"
include "3adant1.mm"
include "ccnv.mm"
include "ismtycnv.mm"
include "3impia.mm"
include "3adant2.mm"
include "syld3an3.mm"
include "impbid.mm"

theorem ismtybnd
  let cF: class F
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( M e. ( *Met ` X ) /\ N e. ( *Met ` Y ) /\ F e. ( M Ismty N ) ) -> ( M e. ( Bnd ` X ) <-> N e. ( Bnd ` Y ) ) )

  proof
    cM
    cX
    cxmt
    cfv
    wcel
    #
    cN
    cY
    cxmt
    cfv
    wcel
    #
    cF
    cM
    cN
    cismty
    co
    wcel
    #
    w3a
    cM
    cX
    cbnd
    cfv
    wcel
    #
    cN
    cY
    cbnd
    cfv
    wcel
    #
    @1
    @2
    @3
    @4
    wi
    @0
    cF
    cM
    cN
    cX
    cY
    ismtybndlem
    3adant1
    @0
    @1
    @2
    cF
    ccnv
    #
    cN
    cM
    cismty
    co
    wcel
    #
    @4
    @3
    wi
    #
    @0
    @1
    @2
    @6
    cF
    cM
    cN
    cX
    cY
    ismtycnv
    3impia
    @0
    @6
    @7
    @1
    @5
    cN
    cM
    cY
    cX
    ismtybndlem
    3adant2
    syld3an3
    impbid
end
