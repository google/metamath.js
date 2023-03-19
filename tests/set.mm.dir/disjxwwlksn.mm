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
include "cword.mm"
include "crab.mm"
include "wss.mm"
include "cwwlksn.mm"
include "wral.mm"
include "wdisj.mm"
include "wi.mm"
include "simp1.mm"
include "a1i.mm"
include "ss2rabi.mm"
include "rgenw.mm"
include "disjxwrd.mm"
include "disjss2.mm"
include "mp2.mm"

theorem disjxwwlksn
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let vf: setvar f
  let vn: setvar n
  let vw: setvar w
  let cW: class W
  assume wwlksnexthasheq.v: |- V = ( Vtx ` G )
  assume wwlksnexthasheq.e: |- E = ( Edg ` G )

  disjoint N y
  disjoint V x
  disjoint x y
  disjoint E f
  disjoint E n
  disjoint E w
  disjoint f n
  disjoint f w
  disjoint n w
  disjoint G f
  disjoint G w
  disjoint N f
  disjoint N w
  disjoint V f
  disjoint V n
  disjoint V w
  disjoint W f
  disjoint W n
  disjoint W w
  assert |- Disj_ y e. ( N WWalksN G ) { x e. Word V | ( ( x substr <. 0 , N >. ) = y /\ ( y ` 0 ) = P /\ { ( lastS ` y ) , ( lastS ` x ) } e. E ) }

  proof
    vx
    cv
    #
    cc0
    cN
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
    cV
    cword
    #
    crab
    #
    @2
    vx
    @6
    crab
    #
    wss
    #
    vy
    cN
    cG
    cwwlksn
    co
    #
    wral
    vy
    @10
    @8
    wdisj
    vy
    @10
    @7
    wdisj
    @9
    vy
    @10
    @5
    @2
    vx
    @6
    @5
    @2
    wi
    @0
    @6
    wcel
    @2
    @3
    @4
    simp1
    a1i
    ss2rabi
    rgenw
    vx
    vy
    cN
    cV
    @10
    disjxwrd
    vy
    @10
    @7
    @8
    disjss2
    mp2
end
