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
include "wn.mm"
include "c0.mm"
include "0ov.mm"
include "cvtx.mm"
include "cmpt2.mm"
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
include "wi.mm"
include "wwlksnon.mm"
include "adantr.mm"
include "eqid.mm"
include "adantl.mm"
include "eqtrd.mm"
include "ex.mm"
include "a1d.mm"
include "pm2.61i.mm"
include "wral.mm"
include "wwlknllvtx.mm"
include "wb.mm"
include "eleq1.mm"
include "eqcoms.mm"
include "bi2anan9.mm"
include "syl5ibrcom.mm"
include "con3rr3.mm"
include "ralrimiv.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "eqtr4d.mm"
include "eqeq2.mm"
include "rabbidv.mm"
include "simprl.mm"
include "simprr.mm"
include "ovex.mm"
include "rabex.mm"
include "a1i.mm"
include "ovmpt2d.mm"
include "ecase.mm"

theorem iswwlksnon
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
  assert |- ( A ( N WWalksNOn G ) B ) = { w e. ( N WWalksN G ) | ( ( w ` 0 ) = A /\ ( w ` N ) = B ) }

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
    @0
    wn
    #
    cA
    cB
    c0
    co
    #
    c0
    @5
    @13
    cA
    cB
    0ov
    #
    @14
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
    @18
    @7
    va
    cv
    #
    wceq
    #
    vn
    cv
    #
    @6
    cfv
    vb
    cv
    #
    wceq
    wa
    vw
    @21
    @17
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
    #
    @14
    @13
    @11
    vw
    c0
    crab
    c0
    @14
    @11
    vw
    @12
    c0
    vn
    vg
    @6
    chash
    cfv
    @21
    c1
    caddc
    co
    wceq
    vw
    @17
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
    @3
    wn
    #
    @5
    c0
    @13
    @0
    @24
    @5
    c0
    wceq
    #
    wi
    @0
    @24
    @25
    @0
    @24
    wa
    #
    @5
    cA
    cB
    va
    vb
    cV
    cV
    @20
    @9
    @22
    wceq
    #
    wa
    #
    vw
    @12
    crab
    #
    cmpt2
    #
    co
    #
    c0
    @26
    @4
    @30
    cA
    cB
    @0
    @4
    @30
    wceq
    #
    @24
    vw
    cvv
    cG
    cN
    cV
    va
    vb
    iswwlksnon.v
    wwlksnon
    #
    adantr
    oveqd
    @24
    @31
    c0
    wceq
    @0
    va
    vb
    @29
    @30
    cA
    cB
    cV
    cV
    @30
    eqid
    mpt2ndm0
    adantl
    eqtrd
    ex
    @14
    @25
    @24
    @14
    @5
    @15
    c0
    @23
    @16
    syl6eq
    a1d
    pm2.61i
    @24
    @11
    wn
    #
    vw
    @12
    wral
    @13
    c0
    wceq
    @24
    @34
    vw
    @12
    @6
    @12
    wcel
    #
    @11
    @3
    @35
    @3
    @11
    @7
    cV
    wcel
    #
    @9
    cV
    wcel
    #
    wa
    cG
    cN
    cV
    @6
    iswwlksnon.v
    wwlknllvtx
    @8
    @1
    @36
    @10
    @2
    @37
    @1
    @36
    wb
    cA
    @7
    cA
    @7
    cV
    eleq1
    eqcoms
    @2
    @37
    wb
    cB
    @9
    cB
    @9
    cV
    eleq1
    eqcoms
    bi2anan9
    syl5ibrcom
    con3rr3
    ralrimiv
    @11
    vw
    @12
    rabeq0
    sylibr
    eqtr4d
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
    @29
    @13
    @4
    cvv
    @0
    @32
    @3
    @33
    adantr
    @19
    cA
    wceq
    #
    @22
    cB
    wceq
    #
    wa
    #
    @29
    @13
    wceq
    @38
    @41
    @28
    @11
    vw
    @12
    @39
    @20
    @8
    @40
    @27
    @10
    @19
    cA
    @7
    eqeq2
    @22
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
    @38
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
    ecase
end
