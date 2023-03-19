include "cr.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "wceq.mm"
include "simp1.mm"
include "simp3.mm"
include "fiminre2.mm"
include "3adant3.mm"
include "infxrre.mm"
include "syl3anc.mm"

theorem infxrrefi
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A C_ RR /\ A e. Fin /\ A =/= (/) ) -> inf ( A , RR* , < ) = inf ( A , RR , < ) )

  proof
    cA
    cr
    wss
    #
    cA
    cfn
    wcel
    #
    cA
    c0
    wne
    #
    w3a
    @0
    @2
    vx
    cv
    vy
    cv
    cle
    wbr
    vy
    cA
    wral
    vx
    cr
    wrex
    #
    cA
    cxr
    clt
    cinf
    cA
    cr
    clt
    cinf
    wceq
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp3
    @0
    @1
    @3
    @2
    vx
    vy
    cA
    fiminre2
    3adant3
    vx
    vy
    cA
    infxrre
    syl3anc
end
