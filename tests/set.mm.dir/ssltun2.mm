include "csslt.mm"
include "wbr.mm"
include "wa.mm"
include "cvv.mm"
include "wcel.mm"
include "cun.mm"
include "csur.mm"
include "wss.mm"
include "cv.mm"
include "cslt.mm"
include "wral.mm"
include "w3a.mm"
include "ssltex1.mm"
include "adantr.mm"
include "ssltex2.mm"
include "unexg.mm"
include "syl2an.mm"
include "jca.mm"
include "ssltss1.mm"
include "ssltss2.mm"
include "adantl.mm"
include "unssd.mm"
include "ssltsep.mm"
include "ralunb.mm"
include "ralbii.mm"
include "r19.26.mm"
include "bitri.mm"
include "sylanbrc.mm"
include "3jca.mm"
include "brsslt.mm"

theorem ssltun2
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A <<s B /\ A <<s C ) -> A <<s ( B u. C ) )

  proof
    cA
    cB
    csslt
    wbr
    #
    cA
    cC
    csslt
    wbr
    #
    wa
    #
    cA
    cvv
    wcel
    #
    cB
    cC
    cun
    #
    cvv
    wcel
    #
    wa
    cA
    csur
    wss
    #
    @4
    csur
    wss
    #
    vx
    cv
    vy
    cv
    cslt
    wbr
    #
    vy
    @4
    wral
    #
    vx
    cA
    wral
    #
    w3a
    cA
    @4
    csslt
    wbr
    @2
    @3
    @5
    @0
    @3
    @1
    cA
    cB
    ssltex1
    adantr
    @0
    cB
    cvv
    wcel
    cC
    cvv
    wcel
    @5
    @1
    cA
    cB
    ssltex2
    cA
    cC
    ssltex2
    cB
    cC
    cvv
    cvv
    unexg
    syl2an
    jca
    @2
    @6
    @7
    @10
    @0
    @6
    @1
    cA
    cB
    ssltss1
    adantr
    @2
    cB
    cC
    csur
    @0
    cB
    csur
    wss
    @1
    cA
    cB
    ssltss2
    adantr
    @1
    cC
    csur
    wss
    @0
    cA
    cC
    ssltss2
    adantl
    unssd
    @2
    @8
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    @8
    vy
    cC
    wral
    #
    vx
    cA
    wral
    #
    @10
    @0
    @12
    @1
    vx
    vy
    cA
    cB
    ssltsep
    adantr
    @1
    @14
    @0
    vx
    vy
    cA
    cC
    ssltsep
    adantl
    @10
    @11
    @13
    wa
    #
    vx
    cA
    wral
    @12
    @14
    wa
    @9
    @15
    vx
    cA
    @8
    vy
    cB
    cC
    ralunb
    ralbii
    @11
    @13
    vx
    cA
    r19.26
    bitri
    sylanbrc
    3jca
    vx
    vy
    cA
    @4
    brsslt
    sylanbrc
end
