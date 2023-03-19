include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "wral.mm"
include "wrex.mm"
include "w3a.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "wcel.mm"
include "wex.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "peano2re.mm"
include "adantr.mm"
include "a1i.mm"
include "ssel.mm"
include "ltp1.mm"
include "ancli.mm"
include "lttr.mm"
include "3expb.mm"
include "sylan2.mm"
include "sylan2i.mm"
include "exp4b.mm"
include "com34.mm"
include "pm2.43d.mm"
include "imp.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "adantl.mm"
include "jaod.mm"
include "ex.mm"
include "syl6.mm"
include "com23.mm"
include "a2d.mm"
include "ralimdv2.mm"
include "expimpd.mm"
include "jcad.mm"
include "ovex.mm"
include "eleq1.mm"
include "breq2.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "spcev.mm"
include "exlimdv.mm"
include "cbvexv.mm"
include "syl6ib.mm"
include "df-rex.mm"
include "3imtr4g.mm"
include "imdistani.mm"
include "df-3an.mm"
include "3imtr4i.mm"
include "axsup.mm"
include "syl.mm"

theorem sup2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint t x
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint t y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint t z
  disjoint v w
  disjoint u w
  disjoint t w
  disjoint A w
  disjoint u v
  disjoint t v
  disjoint A v
  disjoint t u
  disjoint A u
  disjoint A t
  assert |- ( ( A C_ RR /\ A =/= (/) /\ E. x e. RR A. y e. A ( y < x \/ y = x ) ) -> E. x e. RR ( A. y e. A -. x < y /\ A. y e. RR ( y < x -> E. z e. A y < z ) ) )

  proof
    cA
    cr
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
    clt
    wbr
    #
    @2
    @3
    wceq
    #
    wo
    #
    vy
    cA
    wral
    #
    vx
    cr
    wrex
    #
    w3a
    #
    @0
    @1
    @4
    vy
    cA
    wral
    #
    vx
    cr
    wrex
    #
    w3a
    #
    @3
    @2
    clt
    wbr
    wn
    vy
    cA
    wral
    @4
    @2
    vz
    cv
    #
    clt
    wbr
    #
    vz
    cA
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
    @1
    wa
    #
    @8
    wa
    @15
    @11
    wa
    @9
    @12
    @15
    @8
    @11
    @0
    @8
    @11
    wi
    @1
    @0
    @3
    cr
    wcel
    #
    @7
    wa
    #
    vx
    wex
    #
    @16
    @10
    wa
    #
    vx
    wex
    #
    @8
    @11
    @0
    @18
    @13
    cr
    wcel
    #
    @14
    vy
    cA
    wral
    #
    wa
    #
    vz
    wex
    #
    @20
    @0
    @17
    @24
    vx
    @0
    @17
    @3
    c1
    caddc
    co
    #
    cr
    wcel
    #
    @2
    @25
    clt
    wbr
    #
    vy
    cA
    wral
    #
    wa
    #
    @24
    @0
    @17
    @26
    @28
    @17
    @26
    wi
    @0
    @16
    @26
    @7
    @3
    peano2re
    #
    adantr
    a1i
    @0
    @16
    @7
    @28
    @0
    @16
    wa
    #
    @6
    @27
    vy
    cA
    cA
    @31
    @2
    cA
    wcel
    #
    @6
    @27
    @0
    @16
    @32
    @6
    @27
    wi
    #
    wi
    @0
    @32
    @16
    @33
    @0
    @32
    @2
    cr
    wcel
    #
    @16
    @33
    wi
    cA
    cr
    @2
    ssel
    @34
    @16
    @33
    @34
    @16
    wa
    #
    @4
    @27
    @5
    @34
    @16
    @4
    @27
    wi
    #
    @34
    @16
    @36
    @34
    @16
    @4
    @16
    @27
    @34
    @16
    @4
    @16
    @27
    @16
    @35
    @4
    @3
    @25
    clt
    wbr
    #
    @27
    @3
    ltp1
    #
    @16
    @34
    @16
    @26
    wa
    @4
    @37
    wa
    @27
    wi
    #
    @16
    @26
    @30
    ancli
    @34
    @16
    @26
    @39
    @2
    @3
    @25
    lttr
    3expb
    sylan2
    sylan2i
    exp4b
    com34
    pm2.43d
    imp
    @16
    @5
    @27
    wi
    @34
    @16
    @27
    @5
    @37
    @38
    @2
    @3
    @25
    clt
    breq1
    syl5ibrcom
    adantl
    jaod
    ex
    syl6
    com23
    imp
    a2d
    ralimdv2
    expimpd
    jcad
    @23
    @29
    vz
    @25
    @3
    c1
    caddc
    ovex
    @13
    @25
    wceq
    #
    @21
    @26
    @22
    @28
    @13
    @25
    cr
    eleq1
    @40
    @14
    @27
    vy
    cA
    @13
    @25
    @2
    clt
    breq2
    ralbidv
    anbi12d
    spcev
    syl6
    exlimdv
    @23
    @19
    vz
    vx
    @13
    @3
    wceq
    #
    @21
    @16
    @22
    @10
    @13
    @3
    cr
    eleq1
    @41
    @14
    @4
    vy
    cA
    @13
    @3
    @2
    clt
    breq2
    ralbidv
    anbi12d
    cbvexv
    syl6ib
    @7
    vx
    cr
    df-rex
    @10
    vx
    cr
    df-rex
    3imtr4g
    adantr
    imdistani
    @0
    @1
    @8
    df-3an
    @0
    @1
    @11
    df-3an
    3imtr4i
    vx
    vy
    vz
    cA
    axsup
    syl
end
