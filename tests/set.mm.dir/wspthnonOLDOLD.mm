include "wcel.mm"
include "wa.mm"
include "cwwspthsnon.mm"
include "co.mm"
include "cv.mm"
include "cspthson.mm"
include "cfv.mm"
include "wbr.mm"
include "wex.mm"
include "cwwlksnon.mm"
include "crab.mm"
include "iswspthsnonOLD.mm"
include "eleq2d.mm"
include "wceq.mm"
include "breq2.mm"
include "exbidv.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem wspthnonOLDOLD
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let vw: setvar w
  assume wwlknon.v: |- V = ( Vtx ` G )

  disjoint A f
  disjoint B f
  disjoint G f
  disjoint N f
  disjoint V f
  disjoint W f
  disjoint A w
  disjoint B w
  disjoint G w
  disjoint N w
  disjoint W w
  disjoint V w
  disjoint f w
  assert |- ( ( A e. V /\ B e. V ) -> ( W e. ( A ( N WSPathsNOn G ) B ) <-> ( W e. ( A ( N WWalksNOn G ) B ) /\ E. f f ( A ( SPathsOn ` G ) B ) W ) ) )

  proof
    cA
    cV
    wcel
    cB
    cV
    wcel
    wa
    #
    cW
    cA
    cB
    cN
    cG
    cwwspthsnon
    co
    co
    #
    wcel
    cW
    vf
    cv
    #
    vw
    cv
    #
    cA
    cB
    cG
    cspthson
    cfv
    co
    #
    wbr
    #
    vf
    wex
    #
    vw
    cA
    cB
    cN
    cG
    cwwlksnon
    co
    co
    #
    crab
    #
    wcel
    cW
    @7
    wcel
    @2
    cW
    @4
    wbr
    #
    vf
    wex
    #
    wa
    @0
    @1
    @8
    cW
    vw
    cA
    cB
    vf
    cG
    cN
    cV
    wwlknon.v
    iswspthsnonOLD
    eleq2d
    @6
    @10
    vw
    cW
    @7
    @3
    cW
    wceq
    @5
    @9
    vf
    @3
    cW
    @2
    @4
    breq2
    exbidv
    elrab
    syl6bb
end
