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
include "wn.mm"
include "c0.mm"
include "0ov.mm"
include "cvtx.mm"
include "cmpt2.mm"
include "df-wspthsnon.mm"
include "mpt2ndm0.mm"
include "oveqd.mm"
include "id.mm"
include "intnanrd.mm"
include "wwlksnon0.mm"
include "syl.mm"
include "rabeqdv.mm"
include "rab0.mm"
include "syl6eq.mm"
include "3eqtr4a.mm"
include "wi.mm"
include "wspthsnon.mm"
include "adantr.mm"
include "eqid.mm"
include "adantl.mm"
include "eqtrd.mm"
include "ex.mm"
include "a1d.mm"
include "pm2.61i.mm"
include "wral.mm"
include "wal.mm"
include "wwlksonvtx.mm"
include "pm2.24d.mm"
include "impcom.mm"
include "alrimiv.mm"
include "alnex.mm"
include "sylib.mm"
include "ralrimiva.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "eqtr4d.mm"
include "oveq12.mm"
include "breqd.mm"
include "exbidv.mm"
include "rabeqbidv.mm"
include "simprl.mm"
include "simprr.mm"
include "ovex.mm"
include "rabex.mm"
include "a1i.mm"
include "ovmpt2d.mm"
include "ecase.mm"

theorem iswspthsnon
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
  assert |- ( A ( N WSPathsNOn G ) B ) = { w e. ( A ( N WWalksNOn G ) B ) | E. f f ( A ( SPathsOn ` G ) B ) w }

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
    @14
    cA
    cB
    0ov
    #
    @15
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
    @19
    @6
    @7
    va
    cv
    #
    vb
    cv
    #
    @18
    cspthson
    cfv
    co
    wbr
    vf
    wex
    vw
    @20
    @21
    vn
    cv
    @18
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
    #
    @15
    @14
    @11
    vw
    c0
    crab
    c0
    @15
    @11
    vw
    @13
    c0
    @15
    @0
    @3
    wa
    #
    wn
    @13
    c0
    wceq
    @15
    @0
    @3
    @15
    id
    intnanrd
    cA
    cB
    cG
    cN
    cV
    iswspthsnon.v
    wwlksnon0
    syl
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
    @14
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
    @6
    @7
    @20
    @21
    @8
    co
    #
    wbr
    #
    vf
    wex
    #
    vw
    @20
    @21
    @12
    co
    #
    crab
    #
    cmpt2
    #
    co
    #
    c0
    @26
    @4
    @32
    cA
    cB
    @0
    @4
    @32
    wceq
    #
    @24
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
    #
    adantr
    oveqd
    @24
    @33
    c0
    wceq
    @0
    va
    vb
    @31
    @32
    cA
    cB
    cV
    cV
    @32
    eqid
    mpt2ndm0
    adantl
    eqtrd
    ex
    @15
    @25
    @24
    @15
    @5
    @16
    c0
    @22
    @17
    syl6eq
    a1d
    pm2.61i
    @24
    @11
    wn
    #
    vw
    @13
    wral
    @14
    c0
    wceq
    @24
    @36
    vw
    @13
    @24
    @7
    @13
    wcel
    #
    wa
    #
    @10
    wn
    #
    vf
    wal
    @36
    @38
    @39
    vf
    @37
    @24
    @39
    @37
    @3
    @39
    cA
    cB
    cG
    cN
    cV
    @7
    iswspthsnon.v
    wwlksonvtx
    pm2.24d
    impcom
    alrimiv
    @10
    vf
    alnex
    sylib
    ralrimiva
    @11
    vw
    @13
    rabeq0
    sylibr
    eqtr4d
    @23
    va
    vb
    cA
    cB
    cV
    cV
    @31
    @14
    @4
    cvv
    @0
    @34
    @3
    @35
    adantr
    @20
    cA
    wceq
    @21
    cB
    wceq
    wa
    #
    @31
    @14
    wceq
    @23
    @40
    @29
    @11
    vw
    @30
    @13
    @20
    cA
    @21
    cB
    @12
    oveq12
    @40
    @28
    @10
    vf
    @40
    @27
    @9
    @6
    @7
    @20
    cA
    @21
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
    @23
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
    ecase
end
