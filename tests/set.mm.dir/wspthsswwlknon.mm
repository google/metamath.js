include "cwwspthsnon.mm"
include "co.mm"
include "cwwlksnon.mm"
include "cv.mm"
include "wcel.mm"
include "cn0.mm"
include "cvv.mm"
include "wa.mm"
include "cvtx.mm"
include "cfv.mm"
include "cspthson.mm"
include "wbr.mm"
include "wex.mm"
include "w3a.mm"
include "eqid.mm"
include "wspthnonp.mm"
include "simp3l.mm"
include "syl.mm"
include "ssriv.mm"

theorem wspthsswwlknon
  let cA: class A
  let cB: class B
  let cG: class G
  let cN: class N
  let vf: setvar f
  let vw: setvar w


  assert |- ( A ( N WSPathsNOn G ) B ) C_ ( A ( N WWalksNOn G ) B )

  proof
    vw
    cA
    cB
    cN
    cG
    cwwspthsnon
    co
    co
    #
    cA
    cB
    cN
    cG
    cwwlksnon
    co
    co
    #
    vw
    cv
    #
    @0
    wcel
    cN
    cn0
    wcel
    cG
    cvv
    wcel
    wa
    #
    cA
    cG
    cvtx
    cfv
    #
    wcel
    cB
    @4
    wcel
    wa
    #
    @2
    @1
    wcel
    #
    vf
    cv
    @2
    cA
    cB
    cG
    cspthson
    cfv
    co
    wbr
    vf
    wex
    #
    wa
    w3a
    @6
    cA
    cB
    vf
    cG
    cN
    @4
    @2
    @4
    eqid
    wspthnonp
    @3
    @5
    @6
    @7
    simp3l
    syl
    ssriv
end
