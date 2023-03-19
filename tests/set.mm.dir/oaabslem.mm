include "com.mm"
include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "coa.mm"
include "co.mm"
include "wss.mm"
include "cv.mm"
include "ciun.mm"
include "wlim.mm"
include "wceq.mm"
include "nnon.mm"
include "limom.mm"
include "jctr.mm"
include "oalim.mm"
include "syl2an.mm"
include "wral.mm"
include "word.mm"
include "ordom.mm"
include "nnacl.mm"
include "ordelss.mm"
include "sylancr.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "adantr.mm"
include "eqsstrd.mm"
include "ancoms.mm"
include "oaword2.mm"
include "sylan2.mm"
include "eqssd.mm"

theorem oaabslem
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C


  assert |- ( ( _om e. On /\ A e. _om ) -> ( A +o _om ) = _om )

  proof
    com
    con0
    wcel
    #
    cA
    com
    wcel
    #
    wa
    cA
    com
    coa
    co
    #
    com
    @1
    @0
    @2
    com
    wss
    @1
    @0
    wa
    @2
    vx
    com
    cA
    vx
    cv
    #
    coa
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
    @2
    @5
    wceq
    @0
    cA
    nnon
    #
    @0
    @7
    limom
    jctr
    vx
    cA
    com
    con0
    oalim
    syl2an
    @1
    @5
    com
    wss
    #
    @0
    @1
    @4
    com
    wss
    #
    vx
    com
    wral
    @9
    @1
    @10
    vx
    com
    @1
    @3
    com
    wcel
    wa
    com
    word
    @4
    com
    wcel
    @10
    ordom
    cA
    @3
    nnacl
    com
    @4
    ordelss
    sylancr
    ralrimiva
    vx
    com
    @4
    com
    iunss
    sylibr
    adantr
    eqsstrd
    ancoms
    @1
    @0
    @6
    com
    @2
    wss
    @8
    com
    cA
    oaword2
    sylan2
    eqssd
end
