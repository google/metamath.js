include "cn0.mm"
include "wcel.mm"
include "cvv.mm"
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
include "wceq.mm"
include "wi.mm"
include "cmpt2.mm"
include "wspthsnon.mm"
include "adantr.mm"
include "oveq12.mm"
include "breqd.mm"
include "exbidv.mm"
include "rabeqbidv.mm"
include "adantl.mm"
include "simprl.mm"
include "simprr.mm"
include "ovex.mm"
include "rabex.mm"
include "a1i.mm"
include "ovmpt2d.mm"
include "ex.mm"
include "wn.mm"
include "c0.mm"
include "0ov.mm"
include "cvtx.mm"
include "df-wspthsnon.mm"
include "mpt2ndm0.mm"
include "oveqd.mm"
include "cc0.mm"
include "cwwlksn.mm"
include "df-wwlksnon.mm"
include "syl6eq.mm"
include "rabeqdv.mm"
include "rab0.mm"
include "3eqtr4a.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem iswspthsnonOLD
  let vw: setvar w
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cG: class G
  let cN: class N
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vn: setvar n
  assume iswspthsnon.v: |- V = ( Vtx ` G )

  disjoint A f
  disjoint A w
  disjoint f w
  disjoint B f
  disjoint B w
  disjoint G f
  disjoint G w
  disjoint N f
  disjoint N w
  disjoint V f
  disjoint V w
  disjoint A a
  disjoint A b
  disjoint a b
  disjoint a f
  disjoint a w
  disjoint b f
  disjoint b w
  disjoint B a
  disjoint B b
  disjoint G a
  disjoint G b
  disjoint N a
  disjoint N b
  disjoint V a
  disjoint V b
  disjoint a g
  disjoint a n
  disjoint b g
  disjoint b n
  disjoint f g
  disjoint f n
  disjoint g n
  disjoint g w
  disjoint n w
  assert |- ( ( A e. V /\ B e. V ) -> ( A ( N WSPathsNOn G ) B ) = { w e. ( A ( N WWalksNOn G ) B ) | E. f f ( A ( SPathsOn ` G ) B ) w } )

  proof
    cN
    cn0
    wcel
    cG
    cvv
    wcel
    wa
    #
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
    cA
    cB
    cN
    cG
    cwwspthsnon
    co
    #
    co
    #
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
    #
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
    #
    co
    #
    crab
    #
    wceq
    #
    wi
    @0
    @3
    @15
    @0
    @3
    wa
    #
    va
    vb
    cA
    cB
    cV
    cV
    @6
    @7
    va
    cv
    #
    vb
    cv
    #
    @8
    co
    #
    wbr
    #
    vf
    wex
    #
    vw
    @17
    @18
    @12
    co
    #
    crab
    #
    @14
    @4
    cvv
    @0
    @4
    va
    vb
    cV
    cV
    @23
    cmpt2
    wceq
    @3
    vw
    cvv
    vf
    cG
    cN
    cV
    va
    vb
    iswspthsnon.v
    wspthsnon
    adantr
    @17
    cA
    wceq
    @18
    cB
    wceq
    wa
    #
    @23
    @14
    wceq
    @16
    @24
    @21
    @11
    vw
    @22
    @13
    @17
    cA
    @18
    cB
    @12
    oveq12
    @24
    @20
    @10
    vf
    @24
    @19
    @9
    @6
    @7
    @17
    cA
    @18
    cB
    @8
    oveq12
    breqd
    exbidv
    rabeqbidv
    adantl
    @0
    @1
    @2
    simprl
    @0
    @1
    @2
    simprr
    @14
    cvv
    wcel
    @16
    @11
    vw
    @13
    cA
    cB
    @12
    ovex
    rabex
    a1i
    ovmpt2d
    ex
    @0
    wn
    #
    @15
    @3
    @25
    cA
    cB
    c0
    co
    #
    c0
    @5
    @14
    cA
    cB
    0ov
    #
    @25
    @4
    c0
    cA
    cB
    vn
    vg
    va
    vb
    vg
    cv
    #
    cvtx
    cfv
    #
    @29
    @6
    @7
    @17
    @18
    @28
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
    @28
    cwwlksnon
    co
    co
    crab
    cmpt2
    cwwspthsnon
    cN
    cG
    cn0
    cvv
    vw
    vf
    vg
    vn
    va
    vb
    df-wspthsnon
    mpt2ndm0
    oveqd
    @25
    @14
    @11
    vw
    c0
    crab
    c0
    @25
    @11
    vw
    @13
    c0
    @25
    @13
    @26
    c0
    @25
    @12
    c0
    cA
    cB
    vn
    vg
    va
    vb
    @29
    @29
    cc0
    @7
    cfv
    @17
    wceq
    @30
    @7
    cfv
    @18
    wceq
    wa
    vw
    @30
    @28
    cwwlksn
    co
    crab
    cmpt2
    cwwlksnon
    cN
    cG
    cn0
    cvv
    vw
    vg
    vn
    va
    vb
    df-wwlksnon
    mpt2ndm0
    oveqd
    @27
    syl6eq
    rabeqdv
    @11
    vw
    rab0
    syl6eq
    3eqtr4a
    a1d
    pm2.61i
end
