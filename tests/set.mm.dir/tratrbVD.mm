include "wtr.mm"
include "wel.mm"
include "weq.mm"
include "w3o.mm"
include "wral.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "hbra1.mm"
include "alrim3con13v.mm"
include "e0a.mm"
include "ax-5.mm"
include "hbral.mm"
include "wn.mm"
include "wceq.mm"
include "idn2.mm"
include "simpl.mm"
include "e2.mm"
include "simpr.mm"
include "idn3.mm"
include "pm3.2an3.mm"
include "e223.mm"
include "in3.mm"
include "en3lp.mm"
include "con3.mm"
include "e20.mm"
include "eleq2.mm"
include "biimprcd.mm"
include "e23.mm"
include "pm3.2.mm"
include "en2lp.mm"
include "wsbc.mm"
include "idn1.mm"
include "simp3.mm"
include "e1a.mm"
include "simp2.mm"
include "ralcom2.mm"
include "simp1.mm"
include "trel.mm"
include "expd.mm"
include "e121.mm"
include "e122.mm"
include "rspsbc2.mm"
include "com13.mm"
include "wb.mm"
include "equid.mm"
include "sbceq2a.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "sbcoreleleq.mm"
include "biimpd.mm"
include "e12.mm"
include "3ornot23.mm"
include "ex.mm"
include "e222.mm"
include "in2.mm"
include "gen11nv.mm"
include "dftr2.mm"
include "biimpri.mm"
include "in1.mm"

theorem tratrbVD
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  assert |- ( ( Tr A /\ A. x e. A A. y e. A ( x e. y \/ y e. x \/ x = y ) /\ B e. A ) -> Tr B )

  proof
    cA
    wtr
    #
    vx
    vy
    wel
    #
    vy
    vx
    wel
    #
    vx
    vy
    weq
    w3o
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    cB
    cA
    wcel
    #
    w3a
    #
    cB
    wtr
    #
    @7
    @1
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    vx
    cv
    #
    cB
    wcel
    #
    wi
    #
    vy
    wal
    #
    vx
    wal
    #
    @8
    @7
    @15
    vx
    @5
    @5
    vx
    wal
    wi
    @7
    @7
    vx
    wal
    wi
    @4
    vx
    cA
    hbra1
    @5
    @0
    @6
    vx
    alrim3con13v
    e0a
    @7
    @14
    vy
    @5
    @5
    vy
    wal
    wi
    @7
    @7
    vy
    wal
    wi
    @4
    vy
    vx
    cA
    @12
    cA
    wcel
    #
    vy
    ax-5
    @3
    vy
    cA
    hbra1
    hbral
    @5
    @0
    @6
    vy
    alrim3con13v
    e0a
    @7
    @11
    @13
    @7
    @11
    cB
    @12
    wcel
    #
    wn
    #
    @12
    cB
    wceq
    #
    wn
    #
    @13
    @18
    @20
    w3o
    #
    @13
    @7
    @11
    @18
    @1
    @10
    @18
    w3a
    #
    wi
    @23
    wn
    @19
    @7
    @11
    @18
    @23
    @7
    @11
    @1
    @10
    @18
    @18
    @23
    @7
    @11
    @11
    @1
    @7
    @11
    idn2
    #
    @1
    @10
    simpl
    e2
    #
    @7
    @11
    @11
    @10
    @24
    @1
    @10
    simpr
    e2
    #
    @7
    @11
    @18
    idn3
    @1
    @10
    @18
    pm3.2an3
    e223
    in3
    @12
    @9
    cB
    en3lp
    @18
    @23
    con3
    e20
    @7
    @11
    @20
    @1
    @2
    wa
    #
    wi
    @27
    wn
    @21
    @7
    @11
    @20
    @27
    @7
    @11
    @1
    @20
    @2
    @27
    @25
    @7
    @11
    @10
    @20
    @20
    @2
    @26
    @7
    @11
    @20
    idn3
    @20
    @2
    @10
    @12
    cB
    @9
    eleq2
    biimprcd
    e23
    @1
    @2
    pm3.2
    e23
    in3
    @12
    @9
    en2lp
    @20
    @27
    con3
    e20
    @7
    @6
    @11
    @3
    vy
    cB
    wsbc
    #
    @22
    @7
    @7
    @6
    @7
    idn1
    #
    @0
    @5
    @6
    simp3
    e1a
    #
    @7
    @11
    @28
    vx
    @12
    wsbc
    #
    @28
    @7
    @3
    vx
    cA
    wral
    vy
    cA
    wral
    #
    @11
    @17
    @6
    @31
    @7
    @5
    @32
    @7
    @7
    @5
    @29
    @0
    @5
    @6
    simp2
    e1a
    @3
    vx
    vy
    cA
    ralcom2
    e1a
    @7
    @0
    @11
    @1
    @9
    cA
    wcel
    #
    @17
    @7
    @7
    @0
    @29
    @0
    @5
    @6
    simp1
    e1a
    #
    @25
    @7
    @0
    @11
    @10
    @6
    @33
    @34
    @26
    @30
    @0
    @10
    @6
    @33
    cA
    @9
    cB
    trel
    expd
    e121
    @0
    @1
    @33
    @17
    cA
    @12
    @9
    trel
    expd
    e122
    @30
    @6
    @17
    @32
    @31
    @3
    vy
    vx
    cB
    cA
    @12
    cA
    rspsbc2
    com13
    e121
    @31
    @28
    vx
    vx
    weq
    @31
    @28
    wb
    vx
    equid
    @28
    vx
    @12
    sbceq2a
    ax-mp
    biimpi
    e2
    @6
    @28
    @22
    vx
    vy
    cB
    cA
    sbcoreleleq
    biimpd
    e12
    @19
    @21
    @22
    @13
    wi
    @18
    @20
    @13
    3ornot23
    ex
    e222
    in2
    gen11nv
    gen11nv
    @8
    @16
    vx
    vy
    cB
    dftr2
    biimpri
    e1a
    in1
end
