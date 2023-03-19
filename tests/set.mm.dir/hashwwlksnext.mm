include "cvtx.mm"
include "cfv.mm"
include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "co.mm"
include "wceq.mm"
include "clsw.mm"
include "cpr.mm"
include "w3a.mm"
include "cwwlksn.mm"
include "crab.mm"
include "wss.mm"
include "wwlksnfi.mm"
include "ssrab2.mm"
include "ssfi.mm"
include "sylancl.mm"
include "syl5eqel.mm"
include "c1.mm"
include "caddc.mm"
include "rabfi.mm"
include "syl.mm"
include "adantr.mm"
include "wdisj.mm"
include "disjxwwlkn.mm"
include "a1i.mm"
include "hashrabrex.mm"

theorem hashwwlksnext
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cP: class P
  let cE: class E
  let cG: class G
  let cM: class M
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
  disjoint G x
  disjoint M y
  disjoint X x
  disjoint G y
  disjoint Y x
  disjoint G i
  disjoint E i
  disjoint N i
  disjoint W i
  disjoint W w
  assert |- ( ( Vtx ` G ) e. Fin -> ( # ` { x e. X | E. y e. Y ( ( x substr <. 0 , M >. ) = y /\ ( y ` 0 ) = P /\ { ( lastS ` y ) , ( lastS ` x ) } e. E ) } ) = sum_ y e. Y ( # ` { x e. X | ( ( x substr <. 0 , M >. ) = y /\ ( y ` 0 ) = P /\ { ( lastS ` y ) , ( lastS ` x ) } e. E ) } ) )

  proof
    cG
    cvtx
    cfv
    cfn
    wcel
    #
    vx
    cv
    #
    cc0
    cM
    cop
    csubstr
    co
    vy
    cv
    #
    wceq
    cc0
    @2
    cfv
    cP
    wceq
    @2
    clsw
    cfv
    @1
    clsw
    cfv
    cpr
    cE
    wcel
    w3a
    #
    vx
    vy
    cX
    cY
    @0
    cY
    cc0
    vw
    cv
    cfv
    cP
    wceq
    #
    vw
    cN
    cG
    cwwlksn
    co
    #
    crab
    #
    cfn
    wwlksnextprop.y
    @0
    @5
    cfn
    wcel
    @6
    @5
    wss
    @6
    cfn
    wcel
    cG
    cN
    wwlksnfi
    @4
    vw
    @5
    ssrab2
    @5
    @6
    ssfi
    sylancl
    syl5eqel
    @0
    @3
    vx
    cX
    crab
    #
    cfn
    wcel
    #
    @2
    cY
    wcel
    @0
    cX
    cfn
    wcel
    @8
    @0
    cX
    cN
    c1
    caddc
    co
    #
    cG
    cwwlksn
    co
    cfn
    wwlksnextprop.x
    cG
    @9
    wwlksnfi
    syl5eqel
    @3
    vx
    cX
    rabfi
    syl
    adantr
    vy
    cY
    @7
    wdisj
    @0
    vx
    vy
    vw
    cP
    cE
    cG
    cM
    cN
    cX
    cY
    wwlksnextprop.x
    wwlksnextprop.e
    wwlksnextprop.y
    disjxwwlkn
    a1i
    hashrabrex
end
