include "w-bnj15.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wn.mm"
include "wrex.mm"
include "w3a.mm"
include "cv.mm"
include "crab.mm"
include "wcel.mm"
include "wbr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "simp1.mm"
include "ssrab2.mm"
include "a1i.mm"
include "simp3.mm"
include "rabn0.mm"
include "sylibr.mm"
include "nfrab1.mm"
include "nfcrii.mm"
include "bnj1228.mm"
include "syl3anc.mm"
include "biid.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfre1.mm"
include "nf3an.mm"
include "nf5ri.mm"
include "bnj1521.mm"
include "eqid.mm"
include "bnj1212.mm"
include "wsbc.mm"
include "wal.mm"
include "bnj1211.mm"
include "con2b.mm"
include "albii.mm"
include "sylib.mm"
include "simp2.mm"
include "sp.mm"
include "sylc.mm"
include "nfcv.mm"
include "elrabsf.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "sbcng.mm"
include "ax-mp.mm"
include "anbi2i.mm"
include "bitri.mm"
include "notbii.mm"
include "imnan.mm"
include "sylbb2.mm"
include "imp.mm"
include "notnotrd.mm"
include "syl2anc.mm"
include "3expa.mm"
include "expcom.mm"
include "expd.mm"
include "ralrimi.mm"
include "3ad2ant3.mm"
include "simp12.mm"
include "syl3c.mm"
include "rabid.mm"
include "simprbi.mm"
include "3ad2ant2.mm"
include "bnj1304.mm"
include "bnj1224.mm"
include "dfral2.mm"

theorem bnj1204
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vz: setvar z
  assume bnj1204.1: |- ( ps <-> A. y e. A ( y R x -> [. y / x ]. ph ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint ph y
  disjoint A z
  disjoint x z
  disjoint y z
  disjoint R z
  disjoint ph z
  assert |- ( ( R _FrSe A /\ A. x e. A ( ps -> ph ) ) -> A. x e. A ph )

  proof
    cA
    cR
    w-bnj15
    #
    wps
    wph
    wi
    #
    vx
    cA
    wral
    #
    wa
    wph
    wn
    #
    vx
    cA
    wrex
    #
    wn
    wph
    vx
    cA
    wral
    @0
    @2
    @4
    @0
    @2
    @4
    w3a
    #
    @5
    vx
    cv
    #
    @3
    vx
    cA
    crab
    #
    wcel
    #
    vy
    cv
    #
    @6
    cR
    wbr
    #
    wn
    #
    vy
    @7
    wral
    #
    w3a
    #
    wph
    vx
    @12
    @5
    @13
    vx
    @7
    @5
    @0
    @7
    cA
    wss
    #
    @7
    c0
    wne
    #
    @12
    vx
    @7
    wrex
    @0
    @2
    @4
    simp1
    @14
    @5
    @3
    vx
    cA
    ssrab2
    a1i
    @5
    @4
    @15
    @0
    @2
    @4
    simp3
    @3
    vx
    cA
    rabn0
    sylibr
    vx
    vy
    vz
    cA
    @7
    cR
    vx
    vz
    @7
    @3
    vx
    cA
    nfrab1
    nfcrii
    bnj1228
    syl3anc
    @13
    biid
    #
    @5
    vx
    @0
    @2
    @4
    vx
    @0
    vx
    nfv
    @1
    vx
    cA
    nfra1
    @3
    vx
    cA
    nfre1
    nf3an
    nf5ri
    bnj1521
    @13
    @6
    cA
    wcel
    #
    wps
    @2
    wph
    @3
    @5
    @13
    @12
    vx
    cA
    @7
    @7
    eqid
    @16
    bnj1212
    @12
    @5
    wps
    @8
    @12
    @10
    wph
    vx
    @9
    wsbc
    #
    wi
    #
    vy
    cA
    wral
    wps
    @12
    @19
    vy
    cA
    @11
    vy
    @7
    nfra1
    @12
    @9
    cA
    wcel
    #
    @10
    @18
    @20
    @10
    wa
    @12
    @18
    @20
    @10
    @12
    @18
    @20
    @10
    @12
    w3a
    #
    @9
    @7
    wcel
    #
    wn
    #
    @20
    @18
    @21
    @10
    @23
    wi
    #
    vy
    wal
    #
    @10
    @23
    @21
    @22
    @11
    wi
    #
    vy
    wal
    @25
    @21
    @11
    vy
    @7
    @20
    @10
    @12
    simp3
    bnj1211
    @26
    @24
    vy
    @22
    @10
    con2b
    albii
    sylib
    @20
    @10
    @12
    simp2
    @24
    vy
    sp
    sylc
    @20
    @10
    @12
    simp1
    @23
    @20
    wa
    @18
    @23
    @20
    @18
    wn
    #
    wn
    #
    @23
    @20
    @27
    wa
    #
    wn
    @20
    @28
    wi
    @22
    @29
    @22
    @20
    @3
    vx
    @9
    wsbc
    #
    wa
    @29
    @3
    vx
    @9
    cA
    vx
    cA
    nfcv
    elrabsf
    @30
    @27
    @20
    @9
    cvv
    wcel
    @30
    @27
    wb
    vy
    vex
    wph
    vx
    @9
    cvv
    sbcng
    ax-mp
    anbi2i
    bitri
    notbii
    @20
    @27
    imnan
    sylbb2
    imp
    notnotrd
    syl2anc
    3expa
    expcom
    expd
    ralrimi
    bnj1204.1
    sylibr
    3ad2ant3
    @0
    @2
    @4
    @8
    @12
    simp12
    @17
    wps
    @2
    w3a
    #
    @17
    @1
    wi
    #
    vx
    wal
    @17
    wps
    wph
    @31
    @1
    vx
    cA
    @17
    wps
    @2
    simp3
    bnj1211
    @17
    wps
    @2
    simp1
    @17
    wps
    @2
    simp2
    @32
    vx
    sp
    syl3c
    syl3anc
    @8
    @5
    @3
    @12
    @8
    @17
    @3
    @3
    vx
    cA
    rabid
    simprbi
    3ad2ant2
    bnj1304
    bnj1224
    wph
    vx
    cA
    dfral2
    sylibr
end
