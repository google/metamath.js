include "cn0.mm"
include "cvv.mm"
include "cv.mm"
include "cvtx.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "cwwlksn.mm"
include "co.mm"
include "crab.mm"
include "cmpt2.mm"
include "cwwlksnon.mm"
include "df-wwlksnon.mm"
include "wwlksnon.mm"
include "2mpt20.mm"

theorem wwlksnon0
  let cA: class A
  let cB: class B
  let cG: class G
  let cN: class N
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vn: setvar n
  let vw: setvar w
  assume wwlksnon0.v: |- V = ( Vtx ` G )


  assert |- ( -. ( ( N e. NN0 /\ G e. _V ) /\ ( A e. V /\ B e. V ) ) -> ( A ( N WWalksNOn G ) B ) = (/) )

  proof
    vn
    vg
    vb
    cn0
    cvv
    cV
    cV
    cA
    cB
    va
    vb
    vg
    cv
    #
    cvtx
    cfv
    #
    @1
    cc0
    vw
    cv
    #
    cfv
    va
    cv
    wceq
    #
    vn
    cv
    #
    @2
    cfv
    vb
    cv
    #
    wceq
    wa
    vw
    @4
    @0
    cwwlksn
    co
    crab
    cmpt2
    @3
    cN
    @2
    cfv
    @5
    wceq
    wa
    vw
    cN
    cG
    cwwlksn
    co
    crab
    cwwlksnon
    cN
    cG
    va
    vw
    vg
    vn
    va
    vb
    df-wwlksnon
    vw
    cvv
    cG
    cN
    cV
    va
    vb
    wwlksnon0.v
    wwlksnon
    2mpt20
end
