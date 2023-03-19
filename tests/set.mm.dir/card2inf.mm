include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "con0.mm"
include "wrex.mm"
include "wn.mm"
include "csdm.mm"
include "com.mm"
include "wral.mm"
include "crab.mm"
include "wss.mm"
include "wcel.mm"
include "c0.mm"
include "csuc.mm"
include "breq1.mm"
include "0elon.mm"
include "rspcev.mm"
include "mpan.mm"
include "con3i.mm"
include "cdom.mm"
include "0dom.mm"
include "brsdom.mm"
include "mpbiran.mm"
include "sylibr.mm"
include "wa.mm"
include "sucdom2.mm"
include "ad2antll.mm"
include "wi.mm"
include "nnon.mm"
include "suceloni.mm"
include "ex.mm"
include "3syl.mm"
include "con3dimp.mm"
include "adantrr.mm"
include "sylanbrc.mm"
include "exp32.mm"
include "finds2.mm"
include "com12.mm"
include "ralrimiv.mm"
include "omsson.mm"
include "ssrab.mm"

theorem card2inf
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vn: setvar n
  assume card2inf.1: |- A e. _V

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint A n
  disjoint n x
  disjoint n y
  assert |- ( -. E. y e. On y ~~ A -> _om C_ { x e. On | x ~< A } )

  proof
    vy
    cv
    #
    cA
    cen
    wbr
    #
    vy
    con0
    wrex
    #
    wn
    #
    vx
    cv
    #
    cA
    csdm
    wbr
    #
    vx
    com
    wral
    #
    com
    @5
    vx
    con0
    crab
    wss
    #
    @3
    @5
    vx
    com
    @4
    com
    wcel
    @3
    @5
    @5
    c0
    cA
    csdm
    wbr
    #
    vn
    cv
    #
    cA
    csdm
    wbr
    #
    @9
    csuc
    #
    cA
    csdm
    wbr
    #
    @3
    vx
    vn
    @4
    c0
    cA
    csdm
    breq1
    @4
    @9
    cA
    csdm
    breq1
    @4
    @11
    cA
    csdm
    breq1
    @3
    c0
    cA
    cen
    wbr
    #
    wn
    #
    @8
    @13
    @2
    c0
    con0
    wcel
    @13
    @2
    0elon
    @1
    @13
    vy
    c0
    con0
    @0
    c0
    cA
    cen
    breq1
    rspcev
    mpan
    con3i
    @8
    c0
    cA
    cdom
    wbr
    @14
    cA
    card2inf.1
    0dom
    c0
    cA
    brsdom
    mpbiran
    sylibr
    @9
    com
    wcel
    #
    @3
    @10
    @12
    @15
    @3
    @10
    wa
    wa
    @11
    cA
    cdom
    wbr
    #
    @11
    cA
    cen
    wbr
    #
    wn
    #
    @12
    @10
    @16
    @15
    @3
    @9
    cA
    sucdom2
    ad2antll
    @15
    @3
    @18
    @10
    @15
    @17
    @2
    @15
    @9
    con0
    wcel
    @11
    con0
    wcel
    #
    @17
    @2
    wi
    @9
    nnon
    @9
    suceloni
    @19
    @17
    @2
    @1
    @17
    vy
    @11
    con0
    @0
    @11
    cA
    cen
    breq1
    rspcev
    ex
    3syl
    con3dimp
    adantrr
    @11
    cA
    brsdom
    sylanbrc
    exp32
    finds2
    com12
    ralrimiv
    @7
    com
    con0
    wss
    @6
    omsson
    @5
    vx
    con0
    com
    ssrab
    mpbiran
    sylibr
end
