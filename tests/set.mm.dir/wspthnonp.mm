include "cwwspthsnon.mm"
include "co.mm"
include "wcel.mm"
include "cn0.mm"
include "cvv.mm"
include "wa.mm"
include "cvtx.mm"
include "cfv.mm"
include "cwwlksnon.mm"
include "cv.mm"
include "cspthson.mm"
include "wbr.mm"
include "wex.mm"
include "w3a.mm"
include "wral.mm"
include "wi.mm"
include "fvex.mm"
include "pm3.2i.mm"
include "rgen2w.mm"
include "crab.mm"
include "df-wspthsnon.mm"
include "wceq.mm"
include "fveq2.mm"
include "jca.mm"
include "adantl.mm"
include "el2mpt2cl.mm"
include "ax-mp.mm"
include "simprl.mm"
include "eleq2i.mm"
include "anbi12i.mm"
include "biimpri.mm"
include "wspthnon.mm"
include "biimpi.mm"
include "adantr.mm"
include "3jca.mm"
include "mpdan.mm"

theorem wspthnonp
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let vw: setvar w
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vn: setvar n
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
  disjoint G a
  disjoint G b
  disjoint G g
  disjoint G n
  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a n
  disjoint a w
  disjoint b f
  disjoint b g
  disjoint b n
  disjoint b w
  disjoint f g
  disjoint f n
  disjoint g n
  disjoint g w
  disjoint n w
  disjoint N a
  disjoint N b
  disjoint N g
  disjoint N n
  disjoint V a
  disjoint V b
  assert |- ( W e. ( A ( N WSPathsNOn G ) B ) -> ( ( N e. NN0 /\ G e. _V ) /\ ( A e. V /\ B e. V ) /\ ( W e. ( A ( N WWalksNOn G ) B ) /\ E. f f ( A ( SPathsOn ` G ) B ) W ) ) )

  proof
    cW
    cA
    cB
    cN
    cG
    cwwspthsnon
    co
    co
    wcel
    #
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
    #
    cB
    @2
    wcel
    #
    wa
    #
    wa
    #
    @1
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    wa
    #
    cW
    cA
    cB
    cN
    cG
    cwwlksnon
    co
    co
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
    wbr
    vf
    wex
    wa
    #
    w3a
    vg
    cv
    #
    cvtx
    cfv
    #
    cvv
    wcel
    #
    @14
    wa
    #
    vg
    cvv
    wral
    vn
    cn0
    wral
    @0
    @6
    wi
    @15
    vn
    vg
    cn0
    cvv
    @14
    @14
    @12
    cvtx
    fvex
    #
    @16
    pm3.2i
    rgen2w
    vn
    vg
    vb
    cn0
    cvv
    @13
    @13
    cA
    cB
    cvv
    @10
    vw
    cv
    va
    cv
    #
    vb
    cv
    #
    @12
    cspthson
    cfv
    co
    wbr
    vf
    wex
    vw
    @17
    @18
    vn
    cv
    #
    @12
    cwwlksnon
    co
    co
    crab
    @2
    @2
    cwwspthsnon
    cvv
    cW
    cN
    cG
    va
    vw
    vf
    vg
    vn
    va
    vb
    df-wspthsnon
    @12
    cG
    wceq
    #
    @13
    @2
    wceq
    #
    @21
    wa
    @19
    cN
    wceq
    @20
    @21
    @21
    @12
    cG
    cvtx
    fveq2
    #
    @22
    jca
    adantl
    el2mpt2cl
    ax-mp
    @0
    @6
    wa
    @1
    @9
    @11
    @0
    @1
    @5
    simprl
    @6
    @9
    @0
    @5
    @9
    @1
    @9
    @5
    @7
    @3
    @8
    @4
    cV
    @2
    cA
    wwlknon.v
    eleq2i
    cV
    @2
    cB
    wwlknon.v
    eleq2i
    anbi12i
    biimpri
    adantl
    adantl
    @0
    @11
    @6
    @0
    @11
    cA
    cB
    vf
    cG
    cN
    cW
    wspthnon
    biimpi
    adantr
    3jca
    mpdan
end
