include "cv.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cop.mm"
include "csubstr.mm"
include "wceq.mm"
include "clsw.mm"
include "cfv.mm"
include "cpr.mm"
include "wcel.mm"
include "wa.mm"
include "cwwlksn.mm"
include "crab.mm"
include "cvv.mm"
include "wf1o.mm"
include "wex.mm"
include "chash.mm"
include "ovex.mm"
include "rabex.mm"
include "wwlksnextbij.mm"
include "hasheqf1oi.mm"
include "mpsyl.mm"

theorem wwlksnexthasheq
  let vw: setvar w
  let vn: setvar n
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let vf: setvar f
  assume wwlksnexthasheq.v: |- V = ( Vtx ` G )
  assume wwlksnexthasheq.e: |- E = ( Edg ` G )

  disjoint E n
  disjoint E w
  disjoint n w
  disjoint G w
  disjoint N w
  disjoint V n
  disjoint V w
  disjoint W n
  disjoint W w
  disjoint E f
  disjoint f n
  disjoint f w
  disjoint G f
  disjoint N f
  disjoint V f
  disjoint W f
  assert |- ( W e. ( N WWalksN G ) -> ( # ` { w e. ( ( N + 1 ) WWalksN G ) | ( ( w substr <. 0 , ( N + 1 ) >. ) = W /\ { ( lastS ` W ) , ( lastS ` w ) } e. E ) } ) = ( # ` { n e. V | { ( lastS ` W ) , n } e. E } ) )

  proof
    vw
    cv
    #
    cc0
    cN
    c1
    caddc
    co
    #
    cop
    csubstr
    co
    cW
    wceq
    cW
    clsw
    cfv
    #
    @0
    clsw
    cfv
    cpr
    cE
    wcel
    wa
    #
    vw
    @1
    cG
    cwwlksn
    co
    #
    crab
    #
    cvv
    wcel
    cW
    cN
    cG
    cwwlksn
    co
    wcel
    @5
    @2
    vn
    cv
    cpr
    cE
    wcel
    vn
    cV
    crab
    #
    vf
    cv
    wf1o
    vf
    wex
    @5
    chash
    cfv
    @6
    chash
    cfv
    wceq
    @3
    vw
    @4
    @1
    cG
    cwwlksn
    ovex
    rabex
    vw
    vf
    vn
    cE
    cG
    cN
    cV
    cW
    wwlksnexthasheq.v
    wwlksnexthasheq.e
    wwlksnextbij
    @5
    @6
    vf
    cvv
    hasheqf1oi
    mpsyl
end
