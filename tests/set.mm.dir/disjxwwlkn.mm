include "cv.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "co.mm"
include "wceq.mm"
include "cfv.mm"
include "clsw.mm"
include "cpr.mm"
include "wcel.mm"
include "w3a.mm"
include "crab.mm"
include "cvtx.mm"
include "cword.mm"
include "wss.mm"
include "wral.mm"
include "wdisj.mm"
include "wi.mm"
include "simp1.mm"
include "rgenw.mm"
include "ss2rab.mm"
include "mpbir.mm"
include "c1.mm"
include "caddc.mm"
include "cwwlksn.mm"
include "cwwlks.mm"
include "wwlkssswwlksn.mm"
include "eqid.mm"
include "wwlkssswrd.mm"
include "sstri.mm"
include "eqsstri.mm"
include "rabss2.mm"
include "ax-mp.mm"
include "disjxwrd.mm"
include "disjss2.mm"
include "mp2.mm"

theorem disjxwwlkn
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
  disjoint G i
  disjoint E i
  disjoint N i
  disjoint W i
  disjoint W w
  assert |- Disj_ y e. Y { x e. X | ( ( x substr <. 0 , M >. ) = y /\ ( y ` 0 ) = P /\ { ( lastS ` y ) , ( lastS ` x ) } e. E ) }

  proof
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
    #
    cc0
    @1
    cfv
    cP
    wceq
    #
    @1
    clsw
    cfv
    @0
    clsw
    cfv
    cpr
    cE
    wcel
    #
    w3a
    #
    vx
    cX
    crab
    #
    @2
    vx
    cG
    cvtx
    cfv
    #
    cword
    #
    crab
    #
    wss
    #
    vy
    cY
    wral
    vy
    cY
    @9
    wdisj
    vy
    cY
    @6
    wdisj
    @10
    vy
    cY
    @6
    @2
    vx
    cX
    crab
    #
    @9
    @6
    @11
    wss
    @5
    @2
    wi
    #
    vx
    cX
    wral
    @12
    vx
    cX
    @2
    @3
    @4
    simp1
    rgenw
    @5
    @2
    vx
    cX
    ss2rab
    mpbir
    cX
    @8
    wss
    @11
    @9
    wss
    cX
    cN
    c1
    caddc
    co
    #
    cG
    cwwlksn
    co
    #
    @8
    wwlksnextprop.x
    @14
    cG
    cwwlks
    cfv
    @8
    cG
    @13
    wwlkssswwlksn
    cG
    @7
    @7
    eqid
    wwlkssswrd
    sstri
    eqsstri
    @2
    vx
    cX
    @8
    rabss2
    ax-mp
    sstri
    rgenw
    vx
    vy
    cM
    @7
    cY
    disjxwrd
    vy
    cY
    @6
    @9
    disjss2
    mp2
end
