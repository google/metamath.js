include "cwwlksnon.mm"
include "co.mm"
include "wcel.mm"
include "cwwlksn.mm"
include "cc0.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "cvtx.mm"
include "eqid.mm"
include "iswwlksnon.mm"
include "elrab2.mm"
include "3anass.mm"
include "bitr4i.mm"

theorem wwlknon
  let cA: class A
  let cB: class B
  let cG: class G
  let cN: class N
  let cW: class W
  let vw: setvar w
  let cV: class V


  assert |- ( W e. ( A ( N WWalksNOn G ) B ) <-> ( W e. ( N WWalksN G ) /\ ( W ` 0 ) = A /\ ( W ` N ) = B ) )

  proof
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
    cW
    cN
    cG
    cwwlksn
    co
    #
    wcel
    #
    cc0
    cW
    cfv
    #
    cA
    wceq
    #
    cN
    cW
    cfv
    #
    cB
    wceq
    #
    wa
    #
    wa
    @2
    @4
    @6
    w3a
    cc0
    vw
    cv
    #
    cfv
    #
    cA
    wceq
    #
    cN
    @8
    cfv
    #
    cB
    wceq
    #
    wa
    @7
    vw
    cW
    @1
    @0
    @8
    cW
    wceq
    #
    @10
    @4
    @12
    @6
    @13
    @9
    @3
    cA
    cc0
    @8
    cW
    fveq1
    eqeq1d
    @13
    @11
    @5
    cB
    cN
    @8
    cW
    fveq1
    eqeq1d
    anbi12d
    vw
    cA
    cB
    cG
    cN
    cG
    cvtx
    cfv
    #
    @14
    eqid
    iswwlksnon
    elrab2
    @2
    @4
    @6
    3anass
    bitr4i
end
