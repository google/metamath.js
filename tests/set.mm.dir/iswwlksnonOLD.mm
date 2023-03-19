include "cn0.mm"
include "wcel.mm"
include "cvv.mm"
include "wa.mm"
include "cwwlksnon.mm"
include "co.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cwwlksn.mm"
include "crab.mm"
include "wi.mm"
include "cmpt2.mm"
include "wwlksnon.mm"
include "adantr.mm"
include "eqeq2.mm"
include "bi2anan9.mm"
include "rabbidv.mm"
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
include "df-wwlksnon.mm"
include "mpt2ndm0.mm"
include "oveqd.mm"
include "chash.mm"
include "c1.mm"
include "caddc.mm"
include "cwwlks.mm"
include "df-wwlksn.mm"
include "rabeqdv.mm"
include "rab0.mm"
include "syl6eq.mm"
include "3eqtr4a.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem iswwlksnonOLD
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cG: class G
  let cN: class N
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vn: setvar n
  assume iswwlksnon.v: |- V = ( Vtx ` G )

  disjoint A w
  disjoint B w
  disjoint G w
  disjoint N w
  disjoint V w
  disjoint A a
  disjoint A b
  disjoint a b
  disjoint a w
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
  disjoint g n
  disjoint g w
  disjoint n w
  assert |- ( ( A e. V /\ B e. V ) -> ( A ( N WWalksNOn G ) B ) = { w e. ( N WWalksN G ) | ( ( w ` 0 ) = A /\ ( w ` N ) = B ) } )

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
    cwwlksnon
    co
    #
    co
    #
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
    @6
    cfv
    #
    cB
    wceq
    #
    wa
    #
    vw
    cN
    cG
    cwwlksn
    co
    #
    crab
    #
    wceq
    #
    wi
    @0
    @3
    @14
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
    @7
    va
    cv
    #
    wceq
    #
    @9
    vb
    cv
    #
    wceq
    #
    wa
    #
    vw
    @12
    crab
    #
    @13
    @4
    cvv
    @0
    @4
    va
    vb
    cV
    cV
    @21
    cmpt2
    wceq
    @3
    vw
    cvv
    cG
    cN
    cV
    va
    vb
    iswwlksnon.v
    wwlksnon
    adantr
    @16
    cA
    wceq
    #
    @18
    cB
    wceq
    #
    wa
    #
    @21
    @13
    wceq
    @15
    @24
    @20
    @11
    vw
    @12
    @22
    @17
    @8
    @23
    @19
    @10
    @16
    cA
    @7
    eqeq2
    @18
    cB
    @9
    eqeq2
    bi2anan9
    rabbidv
    adantl
    @0
    @1
    @2
    simprl
    @0
    @1
    @2
    simprr
    @13
    cvv
    wcel
    @15
    @11
    vw
    @12
    cN
    cG
    cwwlksn
    ovex
    rabex
    a1i
    ovmpt2d
    ex
    @0
    wn
    #
    @14
    @3
    @25
    cA
    cB
    c0
    co
    c0
    @5
    @13
    cA
    cB
    0ov
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
    @27
    @17
    vn
    cv
    #
    @6
    cfv
    @18
    wceq
    wa
    vw
    @28
    @26
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
    @25
    @13
    @11
    vw
    c0
    crab
    c0
    @25
    @11
    vw
    @12
    c0
    vn
    vg
    @6
    chash
    cfv
    @28
    c1
    caddc
    co
    wceq
    vw
    @26
    cwwlks
    cfv
    crab
    cwwlksn
    cN
    cG
    cn0
    cvv
    vw
    vg
    vn
    df-wwlksn
    mpt2ndm0
    rabeqdv
    @11
    vw
    rab0
    syl6eq
    3eqtr4a
    a1d
    pm2.61i
end
