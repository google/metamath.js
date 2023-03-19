include "csslt.mm"
include "wbr.mm"
include "wss.mm"
include "wa.mm"
include "cvv.mm"
include "wcel.mm"
include "csur.mm"
include "cv.mm"
include "cslt.mm"
include "wral.mm"
include "w3a.mm"
include "ssltex1.mm"
include "adantr.mm"
include "simpr.mm"
include "ssexd.mm"
include "ssltex2.mm"
include "jca.mm"
include "ssltss1.mm"
include "sstrd.mm"
include "ssltss2.mm"
include "ssltsep.mm"
include "ssralv.mm"
include "mpan9.mm"
include "3jca.mm"
include "brsslt.mm"
include "sylanbrc.mm"

theorem sssslt1
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A <<s B /\ C C_ A ) -> C <<s B )

  proof
    cA
    cB
    csslt
    wbr
    #
    cC
    cA
    wss
    #
    wa
    #
    cC
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    cC
    csur
    wss
    #
    cB
    csur
    wss
    #
    vx
    cv
    vy
    cv
    cslt
    wbr
    vy
    cB
    wral
    #
    vx
    cC
    wral
    #
    w3a
    cC
    cB
    csslt
    wbr
    @2
    @3
    @4
    @2
    cC
    cA
    cvv
    @0
    cA
    cvv
    wcel
    @1
    cA
    cB
    ssltex1
    adantr
    @0
    @1
    simpr
    #
    ssexd
    @0
    @4
    @1
    cA
    cB
    ssltex2
    adantr
    jca
    @2
    @5
    @6
    @8
    @2
    cC
    cA
    csur
    @9
    @0
    cA
    csur
    wss
    @1
    cA
    cB
    ssltss1
    adantr
    sstrd
    @0
    @6
    @1
    cA
    cB
    ssltss2
    adantr
    @0
    @7
    vx
    cA
    wral
    @1
    @8
    vx
    vy
    cA
    cB
    ssltsep
    @7
    vx
    cC
    cA
    ssralv
    mpan9
    3jca
    vx
    vy
    cC
    cB
    brsslt
    sylanbrc
end
