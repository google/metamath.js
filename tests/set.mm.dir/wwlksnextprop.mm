include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cop.mm"
include "csubstr.mm"
include "clsw.mm"
include "cpr.mm"
include "w3a.mm"
include "wrex.mm"
include "wa.mm"
include "eqidd.mm"
include "wwlksnextproplem1.mm"
include "ancoms.mm"
include "adantr.mm"
include "wb.mm"
include "eqeq2.mm"
include "adantl.mm"
include "mpbid.mm"
include "wwlksnextproplem2.mm"
include "simpr.mm"
include "simpll.mm"
include "wwlksnextproplem3.mm"
include "syl3anc.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "fveq2.mm"
include "preq1d.mm"
include "eleq1d.mm"
include "3anbi123d.mm"
include "rspcedv.mm"
include "mp3and.mm"
include "ex.mm"
include "wi.mm"
include "eqcoms.mm"
include "eqcomd.mm"
include "syl5ibr.mm"
include "syl6bi.mm"
include "imp.mm"
include "3adant3.mm"
include "com12.mm"
include "rexlimdva.mm"
include "impbid.mm"
include "rabbidva.mm"

theorem wwlksnextprop
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cP: class P
  let cE: class E
  let cG: class G
  let cN: class N
  let cX: class X
  let cY: class Y
  let vi: setvar i
  let cW: class W
  assume wwlksnextprop.x: |- X = ( ( N + 1 ) WWalksN G )
  assume wwlksnextprop.e: |- E = ( Edg ` G )
  assume wwlksnextprop.y: |- Y = { w e. ( N WWalksN G ) | ( w ` 0 ) = P }

  disjoint G w
  disjoint N w
  disjoint P w
  disjoint E y
  disjoint N x
  disjoint N y
  disjoint x y
  disjoint P y
  disjoint X y
  disjoint Y y
  disjoint w x
  disjoint G i
  disjoint E i
  disjoint N i
  disjoint W i
  disjoint W w
  assert |- ( N e. NN0 -> { x e. X | ( x ` 0 ) = P } = { x e. X | E. y e. Y ( ( x substr <. 0 , ( N + 1 ) >. ) = y /\ ( y ` 0 ) = P /\ { ( lastS ` y ) , ( lastS ` x ) } e. E ) } )

  proof
    cN
    cn0
    wcel
    #
    cc0
    vx
    cv
    #
    cfv
    #
    cP
    wceq
    #
    @1
    cc0
    cN
    c1
    caddc
    co
    cop
    csubstr
    co
    #
    vy
    cv
    #
    wceq
    #
    cc0
    @5
    cfv
    #
    cP
    wceq
    #
    @5
    clsw
    cfv
    #
    @1
    clsw
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    w3a
    #
    vy
    cY
    wrex
    #
    vx
    cX
    @0
    @1
    cX
    wcel
    #
    wa
    #
    @3
    @14
    @16
    @3
    @14
    @16
    @3
    wa
    #
    @4
    @4
    wceq
    #
    cc0
    @4
    cfv
    #
    cP
    wceq
    #
    @4
    clsw
    cfv
    #
    @10
    cpr
    #
    cE
    wcel
    #
    @14
    @17
    @4
    eqidd
    @17
    @19
    @2
    wceq
    #
    @20
    @16
    @24
    @3
    @15
    @0
    @24
    cG
    cN
    @1
    cX
    wwlksnextprop.x
    wwlksnextproplem1
    #
    ancoms
    adantr
    @3
    @24
    @20
    wb
    @16
    @2
    cP
    @19
    eqeq2
    adantl
    mpbid
    @16
    @23
    @3
    @15
    @0
    @23
    cE
    cG
    cN
    @1
    cX
    wwlksnextprop.x
    wwlksnextprop.e
    wwlksnextproplem2
    ancoms
    adantr
    @17
    @13
    @18
    @20
    @23
    w3a
    #
    vy
    @4
    cY
    @17
    @15
    @3
    @0
    @4
    cY
    wcel
    @16
    @15
    @3
    @0
    @15
    simpr
    adantr
    @16
    @3
    simpr
    @0
    @15
    @3
    simpll
    vw
    cP
    cE
    cG
    cN
    @1
    cX
    cY
    wwlksnextprop.x
    wwlksnextprop.e
    wwlksnextprop.y
    wwlksnextproplem3
    syl3anc
    @5
    @4
    wceq
    #
    @13
    @26
    wb
    @17
    @27
    @6
    @18
    @8
    @20
    @12
    @23
    @5
    @4
    @4
    eqeq2
    @27
    @7
    @19
    cP
    cc0
    @5
    @4
    fveq1
    #
    eqeq1d
    @27
    @11
    @22
    cE
    @27
    @9
    @21
    @10
    @5
    @4
    clsw
    fveq2
    preq1d
    eleq1d
    3anbi123d
    adantl
    rspcedv
    mp3and
    ex
    @16
    @13
    @3
    vy
    cY
    @13
    @16
    @5
    cY
    wcel
    #
    wa
    #
    @3
    @6
    @8
    @30
    @3
    wi
    #
    @12
    @6
    @8
    @31
    @6
    @8
    @20
    @31
    @6
    @7
    @19
    cP
    @7
    @19
    wceq
    @5
    @4
    @28
    eqcoms
    eqeq1d
    @30
    @3
    @20
    @2
    @19
    wceq
    #
    @16
    @32
    @29
    @15
    @0
    @32
    @15
    @0
    wa
    @19
    @2
    @25
    eqcomd
    ancoms
    adantr
    @3
    @32
    wb
    cP
    @19
    cP
    @19
    @2
    eqeq2
    eqcoms
    syl5ibr
    syl6bi
    imp
    3adant3
    com12
    rexlimdva
    impbid
    rabbidva
end
