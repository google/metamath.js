include "cv.mm"
include "cspthson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "wex.mm"
include "cwwlksnon.mm"
include "cwwspthsnon.mm"
include "wceq.mm"
include "breq2.mm"
include "exbidv.mm"
include "cvtx.mm"
include "eqid.mm"
include "iswspthsnon.mm"
include "elrab2.mm"

theorem wspthnon
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cG: class G
  let cN: class N
  let cW: class W
  let vw: setvar w
  let cV: class V

  disjoint A f
  disjoint B f
  disjoint G f
  disjoint N f
  disjoint W f
  disjoint A w
  disjoint B w
  disjoint G w
  disjoint N w
  disjoint W w
  disjoint V w
  disjoint f w
  disjoint V f
  assert |- ( W e. ( A ( N WSPathsNOn G ) B ) <-> ( W e. ( A ( N WWalksNOn G ) B ) /\ E. f f ( A ( SPathsOn ` G ) B ) W ) )

  proof
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
    @0
    cW
    @2
    wbr
    #
    vf
    wex
    vw
    cW
    cA
    cB
    cN
    cG
    cwwlksnon
    co
    co
    cA
    cB
    cN
    cG
    cwwspthsnon
    co
    co
    @1
    cW
    wceq
    @3
    @4
    vf
    @1
    cW
    @0
    @2
    breq2
    exbidv
    vw
    cA
    cB
    vf
    cG
    cN
    cG
    cvtx
    cfv
    #
    @5
    eqid
    iswspthsnon
    elrab2
end
