include "cr.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "clt.mm"
include "cinf.mm"
include "simp1.mm"
include "fiminre2.mm"
include "3adant3.mm"
include "simp3.mm"
include "infrelb.mm"
include "syl3anc.mm"

theorem infrefilb
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( B C_ RR /\ B e. Fin /\ A e. B ) -> inf ( B , RR , < ) <_ A )

  proof
    cB
    cr
    wss
    #
    cB
    cfn
    wcel
    #
    cA
    cB
    wcel
    #
    w3a
    @0
    vx
    cv
    vy
    cv
    cle
    wbr
    vy
    cB
    wral
    vx
    cr
    wrex
    #
    @2
    cB
    cr
    clt
    cinf
    cA
    cle
    wbr
    @0
    @1
    @2
    simp1
    @0
    @1
    @3
    @2
    vx
    vy
    cB
    fiminre2
    3adant3
    @0
    @1
    @2
    simp3
    vx
    vy
    cA
    cB
    infrelb
    syl3anc
end
