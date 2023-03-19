include "cupgr.mm"
include "wcel.mm"
include "cfn.mm"
include "w3a.mm"
include "c2.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "chash.mm"
include "finsumvtxdgeven.mm"
include "caddc.mm"
include "co.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "incom.mm"
include "rabnc.mm"
include "eqtri.mm"
include "a1i.mm"
include "cun.mm"
include "rabxm.mm"
include "equncomi.mm"
include "simp2.mm"
include "wa.mm"
include "cvtxdg.mm"
include "cc.mm"
include "fveq1i.mm"
include "cdm.mm"
include "cn0.mm"
include "dmfi.mm"
include "3ad2ant3.mm"
include "eqid.mm"
include "vtxdgfisnn0.mm"
include "sylan.mm"
include "nn0cnd.mm"
include "syl5eqel.mm"
include "fsumsplit.mm"
include "breq2d.mm"
include "cz.mm"
include "rabfi.mm"
include "3ad2ant2.mm"
include "elrabi.mm"
include "syl2an.mm"
include "nn0zd.mm"
include "fsumzcl.mm"
include "adantr.mm"
include "fveq2.mm"
include "notbid.mm"
include "elrab.mm"
include "simprbi.mm"
include "adantl.mm"
include "sumodd.mm"
include "biimpa.mm"
include "sumeven.mm"
include "opeo.mm"
include "syl22anc.mm"
include "ex.mm"
include "con4d.mm"
include "sylbid.mm"
include "mpd.mm"

theorem vtxdgoddnumeven
  let vv: setvar v
  let cD: class D
  let cG: class G
  let cI: class I
  let cV: class V
  let vw: setvar w
  assume finsumvtxdgeven.v: |- V = ( Vtx ` G )
  assume finsumvtxdgeven.i: |- I = ( iEdg ` G )
  assume finsumvtxdgeven.d: |- D = ( VtxDeg ` G )

  disjoint G v
  disjoint V v
  disjoint D v
  disjoint I v
  disjoint D w
  disjoint v w
  disjoint G w
  disjoint I w
  disjoint V w
  assert |- ( ( G e. UPGraph /\ V e. Fin /\ I e. Fin ) -> 2 || ( # ` { v e. V | -. 2 || ( D ` v ) } ) )

  proof
    cG
    cupgr
    wcel
    #
    cV
    cfn
    wcel
    #
    cI
    cfn
    wcel
    #
    w3a
    #
    c2
    cV
    vw
    cv
    #
    cD
    cfv
    #
    vw
    csu
    #
    cdvds
    wbr
    #
    c2
    c2
    vv
    cv
    #
    cD
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    vv
    cV
    crab
    #
    chash
    cfv
    cdvds
    wbr
    #
    vw
    cD
    cG
    cI
    cV
    finsumvtxdgeven.v
    finsumvtxdgeven.i
    finsumvtxdgeven.d
    finsumvtxdgeven
    @3
    @7
    c2
    @12
    @5
    vw
    csu
    #
    @10
    vv
    cV
    crab
    #
    @5
    vw
    csu
    #
    caddc
    co
    #
    cdvds
    wbr
    #
    @13
    @3
    @6
    @17
    c2
    cdvds
    @3
    @12
    @15
    @5
    cV
    vw
    @12
    @15
    cin
    #
    c0
    wceq
    @3
    @19
    @15
    @12
    cin
    c0
    @12
    @15
    incom
    @10
    vv
    cV
    rabnc
    eqtri
    a1i
    cV
    @12
    @15
    cun
    wceq
    @3
    cV
    @15
    @12
    @10
    vv
    cV
    rabxm
    equncomi
    a1i
    @0
    @1
    @2
    simp2
    @3
    @4
    cV
    wcel
    #
    wa
    #
    @5
    @4
    cG
    cvtxdg
    cfv
    #
    cfv
    #
    cc
    @4
    cD
    @22
    finsumvtxdgeven.d
    fveq1i
    #
    @21
    @23
    @3
    cI
    cdm
    #
    cfn
    wcel
    #
    @20
    @23
    cn0
    wcel
    #
    @2
    @0
    @26
    @1
    cI
    dmfi
    3ad2ant3
    #
    @25
    @4
    cG
    cI
    cV
    finsumvtxdgeven.v
    finsumvtxdgeven.i
    @25
    eqid
    vtxdgfisnn0
    #
    sylan
    nn0cnd
    syl5eqel
    fsumsplit
    breq2d
    @3
    @13
    @18
    @3
    @13
    wn
    #
    @18
    wn
    #
    @3
    @30
    wa
    @14
    cz
    wcel
    #
    c2
    @14
    cdvds
    wbr
    #
    wn
    #
    @16
    cz
    wcel
    #
    c2
    @16
    cdvds
    wbr
    #
    @31
    @3
    @32
    @30
    @3
    @12
    @5
    vw
    @1
    @0
    @12
    cfn
    wcel
    @2
    @11
    vv
    cV
    rabfi
    3ad2ant2
    #
    @3
    @4
    @12
    wcel
    #
    wa
    #
    @5
    @23
    cz
    @24
    @39
    @23
    @3
    @26
    @20
    @27
    @38
    @28
    @11
    vv
    @4
    cV
    elrabi
    @29
    syl2an
    nn0zd
    syl5eqel
    #
    fsumzcl
    adantr
    @3
    @30
    @34
    @3
    @13
    @33
    @3
    @12
    @5
    vw
    @37
    @40
    @38
    c2
    @5
    cdvds
    wbr
    #
    wn
    #
    @3
    @38
    @20
    @42
    @11
    @42
    vv
    @4
    cV
    @8
    @4
    wceq
    #
    @10
    @41
    @43
    @9
    @5
    c2
    cdvds
    @8
    @4
    cD
    fveq2
    breq2d
    #
    notbid
    elrab
    simprbi
    adantl
    sumodd
    notbid
    biimpa
    @3
    @35
    @30
    @3
    @15
    @5
    vw
    @1
    @0
    @15
    cfn
    wcel
    @2
    @10
    vv
    cV
    rabfi
    3ad2ant2
    #
    @3
    @4
    @15
    wcel
    #
    wa
    #
    @5
    @23
    cz
    @24
    @47
    @23
    @3
    @26
    @20
    @27
    @46
    @28
    @10
    vv
    @4
    cV
    elrabi
    @29
    syl2an
    nn0zd
    syl5eqel
    #
    fsumzcl
    adantr
    @3
    @36
    @30
    @3
    @15
    @5
    vw
    @45
    @48
    @46
    @41
    @3
    @46
    @20
    @41
    @10
    @41
    vv
    @4
    cV
    @44
    elrab
    simprbi
    adantl
    sumeven
    adantr
    @14
    @16
    opeo
    syl22anc
    ex
    con4d
    sylbid
    mpd
end
