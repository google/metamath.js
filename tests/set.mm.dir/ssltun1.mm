include "csslt.mm"
include "wbr.mm"
include "wa.mm"
include "cun.mm"
include "cvv.mm"
include "wcel.mm"
include "csur.mm"
include "wss.mm"
include "cv.mm"
include "cslt.mm"
include "wral.mm"
include "w3a.mm"
include "ssltex1.mm"
include "unexg.mm"
include "syl2an.mm"
include "ssltex2.mm"
include "adantr.mm"
include "jca.mm"
include "ssltss1.mm"
include "adantl.mm"
include "unssd.mm"
include "ssltss2.mm"
include "ssltsep.mm"
include "ralunb.mm"
include "sylanbrc.mm"
include "3jca.mm"
include "brsslt.mm"

theorem ssltun1
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A <<s C /\ B <<s C ) -> ( A u. B ) <<s C )

  proof
    cA
    cC
    csslt
    wbr
    #
    cB
    cC
    csslt
    wbr
    #
    wa
    #
    cA
    cB
    cun
    #
    cvv
    wcel
    #
    cC
    cvv
    wcel
    #
    wa
    @3
    csur
    wss
    #
    cC
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
    cC
    wral
    #
    vx
    @3
    wral
    #
    w3a
    @3
    cC
    csslt
    wbr
    @2
    @4
    @5
    @0
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    @4
    @1
    cA
    cC
    ssltex1
    cB
    cC
    ssltex1
    cA
    cB
    cvv
    cvv
    unexg
    syl2an
    @0
    @5
    @1
    cA
    cC
    ssltex2
    adantr
    jca
    @2
    @6
    @7
    @9
    @2
    cA
    cB
    csur
    @0
    cA
    csur
    wss
    @1
    cA
    cC
    ssltss1
    adantr
    @1
    cB
    csur
    wss
    @0
    cB
    cC
    ssltss1
    adantl
    unssd
    @1
    @7
    @0
    cB
    cC
    ssltss2
    adantl
    @2
    @8
    vx
    cA
    wral
    #
    @8
    vx
    cB
    wral
    #
    @9
    @0
    @10
    @1
    vx
    vy
    cA
    cC
    ssltsep
    adantr
    @1
    @11
    @0
    vx
    vy
    cB
    cC
    ssltsep
    adantl
    @8
    vx
    cA
    cB
    ralunb
    sylanbrc
    3jca
    vx
    vy
    @3
    cC
    brsslt
    sylanbrc
end
