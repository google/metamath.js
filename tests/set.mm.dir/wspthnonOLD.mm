include "cwwspthsnon.mm"
include "co.mm"
include "wcel.mm"
include "cwwlksnon.mm"
include "cv.mm"
include "cspthson.mm"
include "cfv.mm"
include "wbr.mm"
include "wex.mm"
include "wa.mm"
include "wb.mm"
include "wceq.mm"
include "breq2.mm"
include "exbidv.mm"
include "iswspthsnon.mm"
include "elrab2.mm"
include "idi.mm"

theorem wspthnonOLD
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
  assert |- ( W e. ( A ( N WSPathsNOn G ) B ) <-> ( W e. ( A ( N WWalksNOn G ) B ) /\ E. f f ( A ( SPathsOn ` G ) B ) W ) )

  proof
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
    cA
    cB
    cN
    cG
    cwwlksnon
    co
    co
    #
    wcel
    vf
    cv
    #
    cW
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
    wa
    wb
    @2
    vw
    cv
    #
    @3
    wbr
    #
    vf
    wex
    @5
    vw
    cW
    @1
    @0
    @6
    cW
    wceq
    @7
    @4
    vf
    @6
    cW
    @2
    @3
    breq2
    exbidv
    vw
    cA
    cB
    vf
    cG
    cN
    cV
    wwlknon.v
    iswspthsnon
    elrab2
    idi
end
