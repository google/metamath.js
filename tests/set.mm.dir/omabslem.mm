include "com.mm"
include "con0.mm"
include "wcel.mm"
include "c0.mm"
include "w3a.mm"
include "comu.mm"
include "co.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "ciun.mm"
include "wlim.mm"
include "wceq.mm"
include "nnon.mm"
include "limom.mm"
include "jctr.mm"
include "omlim.mm"
include "syl2an.mm"
include "wral.mm"
include "word.mm"
include "ordom.mm"
include "nnmcl.mm"
include "ordelss.mm"
include "sylancr.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "adantr.mm"
include "eqsstrd.mm"
include "ancoms.mm"
include "3adant3.mm"
include "omword2.mm"
include "3impa.mm"
include "syl3an2.mm"
include "eqssd.mm"

theorem omabslem
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C


  assert |- ( ( _om e. On /\ A e. _om /\ (/) e. A ) -> ( A .o _om ) = _om )

  proof
    com
    con0
    wcel
    #
    cA
    com
    wcel
    #
    c0
    cA
    wcel
    #
    w3a
    cA
    com
    comu
    co
    #
    com
    @0
    @1
    @3
    com
    wss
    #
    @2
    @1
    @0
    @4
    @1
    @0
    wa
    @3
    vx
    com
    cA
    vx
    cv
    #
    comu
    co
    #
    ciun
    #
    com
    @1
    cA
    con0
    wcel
    #
    @0
    com
    wlim
    #
    wa
    @3
    @7
    wceq
    @0
    cA
    nnon
    #
    @0
    @9
    limom
    jctr
    vx
    cA
    com
    con0
    omlim
    syl2an
    @1
    @7
    com
    wss
    #
    @0
    @1
    @6
    com
    wss
    #
    vx
    com
    wral
    @11
    @1
    @12
    vx
    com
    @1
    @5
    com
    wcel
    wa
    com
    word
    @6
    com
    wcel
    @12
    ordom
    cA
    @5
    nnmcl
    com
    @6
    ordelss
    sylancr
    ralrimiva
    vx
    com
    @6
    com
    iunss
    sylibr
    adantr
    eqsstrd
    ancoms
    3adant3
    @1
    @0
    @8
    @2
    com
    @3
    wss
    #
    @10
    @0
    @8
    @2
    @13
    com
    cA
    omword2
    3impa
    syl3an2
    eqssd
end
