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
include "nfv.mm"
include "nfra1.mm"
include "nf3an.mm"
include "nfra2.mm"
include "wn.mm"
include "wceq.mm"
include "simpl.mm"
include "a1i.mm"
include "simpr.mm"
include "pm3.2an3.mm"
include "syl6c.mm"
include "en3lp.mm"
include "con3.mm"
include "syl6mpi.mm"
include "eleq2.mm"
include "biimprcd.mm"
include "syl6.mm"
include "pm3.2.mm"
include "syl10.mm"
include "en2lp.mm"
include "wsbc.mm"
include "simp3.mm"
include "simp1.mm"
include "trel.mm"
include "expd.mm"
include "ee121.mm"
include "ee122.mm"
include "ralcom2.mm"
include "3ad2ant2.mm"
include "rspsbc2.mm"
include "wb.mm"
include "equid.mm"
include "sbceq1a.mm"
include "ax-mp.mm"
include "syl6ibr.mm"
include "sbcoreleleq.mm"
include "biimpd.mm"
include "sylsyld.mm"
include "3ornot23.mm"
include "ex.mm"
include "ee222.mm"
include "alrimi.mm"
include "dftr2.mm"
include "sylibr.mm"

theorem tratrb
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
    cB
    wtr
    @7
    @14
    vx
    @0
    @5
    @6
    vx
    @0
    vx
    nfv
    @4
    vx
    cA
    nfra1
    @6
    vx
    nfv
    nf3an
    @7
    @13
    vy
    @0
    @5
    @6
    vy
    @0
    vy
    nfv
    @3
    vx
    vy
    cA
    cA
    nfra2
    @6
    vy
    nfv
    nf3an
    @7
    @10
    cB
    @11
    wcel
    #
    wn
    #
    @11
    cB
    wceq
    #
    wn
    #
    @12
    @15
    @17
    w3o
    #
    @12
    @7
    @10
    @15
    @1
    @9
    @15
    w3a
    #
    wi
    #
    @20
    wn
    @16
    @7
    @10
    @1
    @9
    @21
    @10
    @1
    wi
    @7
    @1
    @9
    simpl
    a1i
    #
    @10
    @9
    wi
    @7
    @1
    @9
    simpr
    a1i
    #
    @1
    @9
    @15
    pm3.2an3
    syl6c
    @11
    @8
    cB
    en3lp
    @15
    @20
    con3
    syl6mpi
    @7
    @10
    @17
    @1
    @2
    wa
    #
    wi
    @24
    wn
    @18
    @7
    @10
    @1
    @17
    @2
    @24
    @22
    @7
    @10
    @9
    @17
    @2
    wi
    @23
    @17
    @2
    @9
    @11
    cB
    @8
    eleq2
    biimprcd
    syl6
    @1
    @2
    pm3.2
    syl10
    @11
    @8
    en2lp
    @17
    @24
    con3
    syl6mpi
    @7
    @6
    @10
    @3
    vy
    cB
    wsbc
    #
    @19
    @0
    @5
    @6
    simp3
    #
    @7
    @10
    @25
    vx
    @11
    wsbc
    #
    @25
    @7
    @6
    @10
    @11
    cA
    wcel
    #
    @3
    vx
    cA
    wral
    vy
    cA
    wral
    #
    @27
    @26
    @7
    @0
    @10
    @1
    @8
    cA
    wcel
    #
    @28
    @0
    @5
    @6
    simp1
    #
    @22
    @7
    @0
    @10
    @9
    @6
    @30
    @31
    @23
    @26
    @0
    @9
    @6
    @30
    cA
    @8
    cB
    trel
    expd
    ee121
    @0
    @1
    @30
    @28
    cA
    @11
    @8
    trel
    expd
    ee122
    @5
    @0
    @29
    @6
    @3
    vx
    vy
    cA
    ralcom2
    3ad2ant2
    @3
    vy
    vx
    cB
    cA
    @11
    cA
    rspsbc2
    ee121
    vx
    vx
    weq
    @25
    @27
    wb
    vx
    equid
    @25
    vx
    @11
    sbceq1a
    ax-mp
    syl6ibr
    @6
    @25
    @19
    vx
    vy
    cB
    cA
    sbcoreleleq
    biimpd
    sylsyld
    @16
    @18
    @19
    @12
    wi
    @15
    @17
    @12
    3ornot23
    ex
    ee222
    alrimi
    alrimi
    vx
    vy
    cB
    dftr2
    sylibr
end
