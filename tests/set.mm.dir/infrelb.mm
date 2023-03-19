include "cr.mm"
include "wss.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wcel.mm"
include "w3a.mm"
include "clt.mm"
include "cinf.mm"
include "c0.mm"
include "wne.mm"
include "simp1.mm"
include "ne0i.mm"
include "3ad2ant3.mm"
include "simp2.mm"
include "infrecl.mm"
include "syl3anc.mm"
include "ssel2.mm"
include "3adant2.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "wor.mm"
include "ltso.mm"
include "a1i.mm"
include "simpll.mm"
include "adantl.mm"
include "simplr.mm"
include "infm3.mm"
include "inflb.mm"
include "expcom.mm"
include "pm2.43b.mm"
include "3impia.mm"
include "nltled.mm"

theorem infrelb
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint x z
  disjoint y z
  disjoint B z
  assert |- ( ( B C_ RR /\ E. x e. RR A. y e. B x <_ y /\ A e. B ) -> inf ( B , RR , < ) <_ A )

  proof
    cB
    cr
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    vy
    cB
    wral
    vx
    cr
    wrex
    #
    cA
    cB
    wcel
    #
    w3a
    #
    cB
    cr
    clt
    cinf
    #
    cA
    @5
    @0
    cB
    c0
    wne
    #
    @3
    @6
    cr
    wcel
    @0
    @3
    @4
    simp1
    @4
    @0
    @7
    @3
    cB
    cA
    ne0i
    #
    3ad2ant3
    @0
    @3
    @4
    simp2
    vx
    vy
    cB
    infrecl
    syl3anc
    @0
    @4
    cA
    cr
    wcel
    @3
    cB
    cr
    cA
    ssel2
    3adant2
    @0
    @3
    @4
    cA
    @6
    clt
    wbr
    wn
    #
    @0
    @3
    wa
    #
    @4
    @9
    @10
    @4
    @4
    @9
    wi
    @10
    @4
    wa
    #
    vx
    vy
    vz
    cr
    cB
    cA
    clt
    cr
    clt
    wor
    @11
    ltso
    a1i
    @11
    @0
    @7
    @3
    @2
    @1
    clt
    wbr
    wn
    vy
    cB
    wral
    @1
    @2
    clt
    wbr
    vz
    cv
    @2
    clt
    wbr
    vz
    cB
    wrex
    wi
    vy
    cr
    wral
    wa
    vx
    cr
    wrex
    @0
    @3
    @4
    simpll
    @4
    @7
    @10
    @8
    adantl
    @0
    @3
    @4
    simplr
    vx
    vy
    vz
    cB
    infm3
    syl3anc
    inflb
    expcom
    pm2.43b
    3impia
    nltled
end
