include "wwe.mm"
include "wfr.mm"
include "wor.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "weq.mm"
include "w3o.mm"
include "wral.mm"
include "df-we.mm"
include "wpo.mm"
include "df-so.mm"
include "simpr.mm"
include "wn.mm"
include "wi.mm"
include "wcel.mm"
include "w3a.mm"
include "wal.mm"
include "ax-1.mm"
include "a1i.mm"
include "fr2nr.mm"
include "3adantr3.mm"
include "breq2.mm"
include "anbi2d.mm"
include "notbid.mm"
include "syl5ibcom.mm"
include "pm2.21.mm"
include "syl6.mm"
include "fr3nr.mm"
include "df-3an.mm"
include "biimpri.mm"
include "ancoms.mm"
include "nsyl.mm"
include "pm2.21d.mm"
include "expd.mm"
include "3jaod.mm"
include "frirr.mm"
include "3ad2antr1.mm"
include "jctild.mm"
include "ex.mm"
include "a2d.mm"
include "alimdv.mm"
include "2alimdv.mm"
include "r3al.mm"
include "3imtr4g.mm"
include "ralidm.mm"
include "equequ2.mm"
include "breq1.mm"
include "3orbi123d.mm"
include "cbvralv.mm"
include "ralbii.mm"
include "bitr3i.mm"
include "df-po.mm"
include "ancrd.mm"
include "impbid2.mm"
include "syl5bb.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem dfwe2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vz: setvar z

  disjoint x y
  disjoint R x
  disjoint R y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint y z
  disjoint R z
  disjoint A z
  assert |- ( R We A <-> ( R Fr A /\ A. x e. A A. y e. A ( x R y \/ x = y \/ y R x ) ) )

  proof
    cA
    cR
    wwe
    cA
    cR
    wfr
    #
    cA
    cR
    wor
    #
    wa
    @0
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    vx
    vy
    weq
    #
    @3
    @2
    cR
    wbr
    #
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
    wa
    cA
    cR
    df-we
    @0
    @1
    @9
    @1
    cA
    cR
    wpo
    #
    @9
    wa
    #
    @0
    @9
    vx
    vy
    cA
    cR
    df-so
    @0
    @11
    @9
    @10
    @9
    simpr
    @0
    @9
    @10
    @0
    @2
    vz
    cv
    #
    cR
    wbr
    #
    vx
    vz
    weq
    #
    @12
    @2
    cR
    wbr
    #
    w3o
    #
    vz
    cA
    wral
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    @2
    @2
    cR
    wbr
    wn
    #
    @4
    @3
    @12
    cR
    wbr
    #
    wa
    #
    @13
    wi
    #
    wa
    #
    vz
    cA
    wral
    vy
    cA
    wral
    vx
    cA
    wral
    #
    @9
    @10
    @0
    @2
    cA
    wcel
    #
    @3
    cA
    wcel
    #
    @12
    cA
    wcel
    #
    w3a
    #
    @16
    wi
    #
    vz
    wal
    #
    vy
    wal
    vx
    wal
    @29
    @24
    wi
    #
    vz
    wal
    #
    vy
    wal
    vx
    wal
    @19
    @25
    @0
    @31
    @33
    vx
    vy
    @0
    @30
    @32
    vz
    @0
    @29
    @16
    @24
    @0
    @29
    @16
    @24
    wi
    @0
    @29
    wa
    #
    @16
    @23
    @20
    @34
    @13
    @23
    @14
    @15
    @13
    @23
    wi
    @34
    @13
    @22
    ax-1
    a1i
    @34
    @14
    @22
    wn
    #
    @23
    @34
    @4
    @6
    wa
    #
    wn
    #
    @14
    @35
    @0
    @26
    @27
    @37
    @28
    cA
    @2
    @3
    cR
    fr2nr
    3adantr3
    @14
    @36
    @22
    @14
    @6
    @21
    @4
    @2
    @12
    @3
    cR
    breq2
    anbi2d
    notbid
    syl5ibcom
    @22
    @13
    pm2.21
    syl6
    @34
    @15
    @22
    @13
    @34
    @15
    @22
    wa
    #
    @13
    @34
    @4
    @21
    @15
    w3a
    #
    @38
    cA
    @2
    @3
    @12
    cR
    fr3nr
    @22
    @15
    @39
    @39
    @22
    @15
    wa
    @4
    @21
    @15
    df-3an
    biimpri
    ancoms
    nsyl
    pm2.21d
    expd
    3jaod
    @0
    @27
    @26
    @20
    @28
    cA
    @2
    cR
    frirr
    3ad2antr1
    jctild
    ex
    a2d
    alimdv
    2alimdv
    @16
    vx
    vy
    vz
    cA
    cA
    cA
    r3al
    @24
    vx
    vy
    vz
    cA
    cA
    cA
    r3al
    3imtr4g
    @8
    @18
    vx
    cA
    @8
    @8
    vy
    cA
    wral
    @18
    @7
    vy
    cA
    ralidm
    @8
    @17
    vy
    cA
    @7
    @16
    vy
    vz
    cA
    vy
    vz
    weq
    @4
    @13
    @5
    @14
    @6
    @15
    @3
    @12
    @2
    cR
    breq2
    vy
    vz
    vx
    equequ2
    @3
    @12
    @2
    cR
    breq1
    3orbi123d
    cbvralv
    ralbii
    bitr3i
    ralbii
    vx
    vy
    vz
    cA
    cR
    df-po
    3imtr4g
    ancrd
    impbid2
    syl5bb
    pm5.32i
    bitri
end
