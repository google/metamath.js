include "cnq.mm"
include "wcel.mm"
include "c0.mm"
include "cv.mm"
include "cltq.mm"
include "wbr.mm"
include "cab.mm"
include "wpss.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wrex.mm"
include "wral.mm"
include "cnp.mm"
include "wne.mm"
include "wex.mm"
include "nsmallnq.mm"
include "abn0.mm"
include "sylibr.mm"
include "0pss.mm"
include "wss.mm"
include "wn.mm"
include "ltrelnq.mm"
include "brel.mm"
include "simpld.mm"
include "abssi.mm"
include "ltsonq.mm"
include "soirri.mm"
include "breq1.mm"
include "elabg.mm"
include "mtbiri.mm"
include "ancli.mm"
include "ssnelpss.mm"
include "mpsyl.mm"
include "jca.mm"
include "vex.mm"
include "elab.mm"
include "sotri.mm"
include "expcom.mm"
include "adantl.mm"
include "syl6ibr.mm"
include "alrimiv.mm"
include "ltbtwnnq.mm"
include "anbi2i.mm"
include "biimpri.mm"
include "ancomd.mm"
include "eximi.mm"
include "sylbi.mm"
include "df-rex.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "elnp.mm"
include "sylanbrc.mm"

theorem nqpr
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( A e. Q. -> { x | x <Q A } e. P. )

  proof
    cA
    cnq
    wcel
    #
    c0
    vx
    cv
    #
    cA
    cltq
    wbr
    #
    vx
    cab
    #
    wpss
    #
    @3
    cnq
    wpss
    #
    wa
    vz
    cv
    #
    vy
    cv
    #
    cltq
    wbr
    #
    @6
    @3
    wcel
    #
    wi
    #
    vz
    wal
    #
    @7
    @6
    cltq
    wbr
    #
    vz
    @3
    wrex
    #
    wa
    #
    vy
    @3
    wral
    @3
    cnp
    wcel
    @0
    @4
    @5
    @0
    @3
    c0
    wne
    #
    @4
    @0
    @2
    vx
    wex
    @15
    vx
    cA
    nsmallnq
    @2
    vx
    abn0
    sylibr
    @3
    0pss
    sylibr
    @3
    cnq
    wss
    @0
    @0
    cA
    @3
    wcel
    #
    wn
    #
    wa
    @5
    @2
    vx
    cnq
    @2
    @1
    cnq
    wcel
    @0
    @1
    cA
    cnq
    cnq
    cltq
    ltrelnq
    brel
    simpld
    abssi
    @0
    @17
    @0
    @16
    cA
    cA
    cltq
    wbr
    #
    cA
    cltq
    cnq
    ltsonq
    ltrelnq
    soirri
    @2
    @18
    vx
    cA
    cnq
    @1
    cA
    cA
    cltq
    breq1
    elabg
    mtbiri
    ancli
    @3
    cnq
    cA
    ssnelpss
    mpsyl
    jca
    @0
    @14
    vy
    @3
    @7
    @3
    wcel
    @0
    @7
    cA
    cltq
    wbr
    #
    @14
    @2
    @19
    vx
    @7
    vy
    vex
    @1
    @7
    cA
    cltq
    breq1
    elab
    @0
    @19
    wa
    #
    @11
    @13
    @20
    @10
    vz
    @20
    @8
    @6
    cA
    cltq
    wbr
    #
    @9
    @19
    @8
    @21
    wi
    @0
    @8
    @19
    @21
    @6
    @7
    cA
    cltq
    cnq
    ltsonq
    ltrelnq
    sotri
    expcom
    adantl
    @2
    @21
    vx
    @6
    vz
    vex
    @1
    @6
    cA
    cltq
    breq1
    elab
    #
    syl6ibr
    alrimiv
    @20
    @9
    @12
    wa
    #
    vz
    wex
    #
    @13
    @19
    @24
    @0
    @19
    @12
    @21
    wa
    #
    vz
    wex
    @24
    vz
    @7
    cA
    ltbtwnnq
    @25
    @23
    vz
    @25
    @12
    @9
    @12
    @9
    wa
    @25
    @9
    @21
    @12
    @22
    anbi2i
    biimpri
    ancomd
    eximi
    sylbi
    adantl
    @12
    vz
    @3
    df-rex
    sylibr
    jca
    sylan2b
    ralrimiva
    vy
    vz
    @3
    elnp
    sylanbrc
end
