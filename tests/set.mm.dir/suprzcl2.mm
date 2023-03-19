include "cz.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "w3a.mm"
include "clt.mm"
include "wn.mm"
include "wi.mm"
include "cr.mm"
include "wa.mm"
include "csup.mm"
include "wcel.mm"
include "zsupss.mm"
include "wceq.mm"
include "ssel2.mm"
include "zred.mm"
include "wtru.mm"
include "wor.mm"
include "ltso.mm"
include "a1i.mm"
include "eqsup.mm"
include "trud.mm"
include "3expib.mm"
include "syl.mm"
include "simpr.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "syld.mm"
include "rexlimdva.mm"
include "3ad2ant1.mm"
include "mpd.mm"

theorem suprzcl2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vm: setvar m
  let vn: setvar n
  let vw: setvar w
  let vz: setvar z
  let cB: class B
  let cM: class M
  let cZ: class Z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint m n
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B n
  disjoint B x
  disjoint M x
  disjoint M y
  disjoint Z x
  assert |- ( ( A C_ ZZ /\ A =/= (/) /\ E. x e. ZZ A. y e. A y <_ x ) -> sup ( A , RR , < ) e. A )

  proof
    cA
    cz
    wss
    #
    cA
    c0
    wne
    #
    vy
    cv
    #
    vx
    cv
    #
    cle
    wbr
    vy
    cA
    wral
    vx
    cz
    wrex
    #
    w3a
    @3
    @2
    clt
    wbr
    wn
    vy
    cA
    wral
    #
    @2
    @3
    clt
    wbr
    @2
    vz
    cv
    clt
    wbr
    vz
    cA
    wrex
    wi
    vy
    cr
    wral
    #
    wa
    #
    vx
    cA
    wrex
    #
    cA
    cr
    clt
    csup
    #
    cA
    wcel
    #
    vx
    vy
    vz
    cA
    cr
    zsupss
    @0
    @1
    @8
    @10
    wi
    @4
    @0
    @7
    @10
    vx
    cA
    @0
    @3
    cA
    wcel
    #
    wa
    #
    @7
    @9
    @3
    wceq
    #
    @10
    @12
    @3
    cr
    wcel
    #
    @7
    @13
    wi
    @12
    @3
    cA
    cz
    @3
    ssel2
    zred
    @14
    @5
    @6
    @13
    @14
    @5
    @6
    w3a
    @13
    wi
    wtru
    vy
    vz
    cr
    cA
    @3
    clt
    cr
    clt
    wor
    wtru
    ltso
    a1i
    eqsup
    trud
    3expib
    syl
    @12
    @10
    @13
    @11
    @0
    @11
    simpr
    @9
    @3
    cA
    eleq1
    syl5ibrcom
    syld
    rexlimdva
    3ad2ant1
    mpd
end
