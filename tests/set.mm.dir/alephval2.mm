include "con0.mm"
include "wcel.mm"
include "c0.mm"
include "wa.mm"
include "cale.mm"
include "cfv.mm"
include "cv.mm"
include "csdm.mm"
include "wbr.mm"
include "wral.mm"
include "crab.mm"
include "wn.mm"
include "cint.mm"
include "wceq.mm"
include "alephordi.mm"
include "ralrimiv.mm"
include "alephon.mm"
include "jctil.mm"
include "breq2.mm"
include "ralbidv.mm"
include "elrab.mm"
include "sylibr.mm"
include "adantr.mm"
include "ccrd.mm"
include "cardsdomelir.mm"
include "alephcard.mm"
include "eqcomi.mm"
include "eleq2s.mm"
include "com.mm"
include "cdom.mm"
include "wo.mm"
include "wi.mm"
include "cvv.mm"
include "omex.mm"
include "vex.mm"
include "entri3.mm"
include "mp2an.mm"
include "wss.mm"
include "wb.mm"
include "carddom.mm"
include "cardom.mm"
include "sseq1i.mm"
include "bitr3i.mm"
include "wrex.mm"
include "cardidm.mm"
include "cardalephex.mm"
include "mpbii.mm"
include "alephord.mm"
include "ancoms.mm"
include "cen.mm"
include "cardid.mm"
include "sdomen1.mm"
include "ax-mp.mm"
include "breq1.mm"
include "syl5rbbr.mm"
include "sylan9bb.mm"
include "fveq2.mm"
include "breq1d.mm"
include "rspcv.mm"
include "sdomirr.mm"
include "sdomen2.mm"
include "syl5bbr.mm"
include "mtbiri.mm"
include "nsyli.mm"
include "com12.mm"
include "adantl.mm"
include "sylbird.mm"
include "exp31.mm"
include "rexlimdv.mm"
include "syl5.mm"
include "syl5bi.mm"
include "wne.mm"
include "ne0i.mm"
include "onelon.mm"
include "alephgeom.mm"
include "ssdomg.mm"
include "sylbi.mm"
include "domtr.mm"
include "sylan2.mm"
include "domnsym.mm"
include "syl.mm"
include "expr.mm"
include "r19.2z.mm"
include "ex.mm"
include "syl2im.mm"
include "rexnal.mm"
include "syl6ib.mm"
include "expimpd.mm"
include "a1d.mm"
include "com3r.mm"
include "jaod.mm"
include "mpi.mm"
include "simprbi.mm"
include "con3i.mm"
include "syl56.mm"
include "ssrab2.mm"
include "oneqmini.mm"
include "syl2anc.mm"

theorem alephval2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- ( ( A e. On /\ (/) e. A ) -> ( aleph ` A ) = |^| { x e. On | A. y e. A ( aleph ` y ) ~< x } )

  proof
    cA
    con0
    wcel
    #
    c0
    cA
    wcel
    #
    wa
    #
    cA
    cale
    cfv
    #
    vy
    cv
    #
    cale
    cfv
    #
    vx
    cv
    #
    csdm
    wbr
    #
    vy
    cA
    wral
    #
    vx
    con0
    crab
    #
    wcel
    #
    vz
    cv
    #
    @9
    wcel
    #
    wn
    #
    vz
    @3
    wral
    #
    @3
    @9
    cint
    wceq
    #
    @0
    @10
    @1
    @0
    @3
    con0
    wcel
    #
    @5
    @3
    csdm
    wbr
    #
    vy
    cA
    wral
    #
    wa
    @10
    @0
    @18
    @16
    @0
    @17
    vy
    cA
    @4
    cA
    alephordi
    ralrimiv
    cA
    alephon
    jctil
    @8
    @18
    vx
    @3
    con0
    @6
    @3
    wceq
    @7
    @17
    vy
    cA
    @6
    @3
    @5
    csdm
    breq2
    ralbidv
    elrab
    sylibr
    adantr
    @2
    @13
    vz
    @3
    @11
    @3
    wcel
    @11
    @3
    csdm
    wbr
    #
    @2
    @5
    @11
    csdm
    wbr
    #
    vy
    cA
    wral
    #
    wn
    #
    @13
    @19
    @11
    @3
    ccrd
    cfv
    #
    @3
    @11
    @3
    cardsdomelir
    @23
    @3
    cA
    alephcard
    eqcomi
    eleq2s
    @2
    com
    @11
    cdom
    wbr
    #
    @11
    com
    cdom
    wbr
    #
    wo
    #
    @19
    @22
    wi
    #
    com
    cvv
    wcel
    #
    @11
    cvv
    wcel
    #
    @26
    omex
    vz
    vex
    #
    com
    @11
    cvv
    cvv
    entri3
    mp2an
    @2
    @24
    @27
    @25
    @0
    @24
    @27
    wi
    @1
    @24
    com
    @11
    ccrd
    cfv
    #
    wss
    #
    @0
    @27
    @24
    com
    ccrd
    cfv
    #
    @31
    wss
    #
    @32
    @28
    @29
    @34
    @24
    wb
    omex
    @30
    com
    @11
    cvv
    cvv
    carddom
    mp2an
    @33
    com
    @31
    cardom
    sseq1i
    bitr3i
    @32
    @31
    @6
    cale
    cfv
    #
    wceq
    #
    vx
    con0
    wrex
    #
    @0
    @27
    @32
    @31
    ccrd
    cfv
    @31
    wceq
    @37
    @11
    cardidm
    vx
    @31
    cardalephex
    mpbii
    @0
    @36
    @27
    vx
    con0
    @0
    @6
    con0
    wcel
    #
    @36
    @27
    @0
    @38
    wa
    #
    @36
    wa
    @19
    @6
    cA
    wcel
    #
    @22
    @39
    @40
    @35
    @3
    csdm
    wbr
    #
    @36
    @19
    @38
    @0
    @40
    @41
    wb
    @6
    cA
    alephord
    ancoms
    @19
    @31
    @3
    csdm
    wbr
    #
    @36
    @41
    @31
    @11
    cen
    wbr
    #
    @42
    @19
    wb
    @11
    @30
    cardid
    #
    @31
    @11
    @3
    sdomen1
    ax-mp
    @31
    @35
    @3
    csdm
    breq1
    syl5rbbr
    sylan9bb
    @36
    @40
    @22
    wi
    @39
    @40
    @36
    @22
    @40
    @21
    @35
    @11
    csdm
    wbr
    #
    @36
    @20
    @45
    vy
    @6
    cA
    @4
    @6
    wceq
    @5
    @35
    @11
    csdm
    @4
    @6
    cale
    fveq2
    breq1d
    rspcv
    @36
    @45
    @35
    @35
    csdm
    wbr
    #
    @35
    sdomirr
    @45
    @35
    @31
    csdm
    wbr
    #
    @36
    @46
    @43
    @47
    @45
    wb
    @44
    @31
    @11
    @35
    sdomen2
    ax-mp
    @31
    @35
    @35
    csdm
    breq2
    syl5bbr
    mtbiri
    nsyli
    com12
    adantl
    sylbird
    exp31
    rexlimdv
    syl5
    syl5bi
    adantr
    @25
    @19
    @2
    @22
    @25
    @2
    @22
    wi
    @19
    @25
    @0
    @1
    @22
    @1
    @25
    @0
    wa
    #
    @22
    @1
    @48
    @20
    wn
    #
    vy
    cA
    wrex
    #
    @22
    @1
    cA
    c0
    wne
    #
    @48
    @49
    vy
    cA
    wral
    #
    @50
    cA
    c0
    ne0i
    @48
    @49
    vy
    cA
    @25
    @0
    @4
    cA
    wcel
    #
    @49
    @0
    @53
    wa
    @25
    @4
    con0
    wcel
    #
    @49
    cA
    @4
    onelon
    @25
    @54
    wa
    @11
    @5
    cdom
    wbr
    #
    @49
    @54
    @25
    com
    @5
    cdom
    wbr
    #
    @55
    @54
    com
    @5
    wss
    #
    @56
    @4
    alephgeom
    @5
    con0
    wcel
    @57
    @56
    wi
    @4
    alephon
    com
    @5
    con0
    ssdomg
    ax-mp
    sylbi
    @11
    com
    @5
    domtr
    sylan2
    @11
    @5
    domnsym
    syl
    sylan2
    expr
    ralrimiv
    @51
    @52
    @50
    @49
    vy
    cA
    r19.2z
    ex
    syl2im
    @20
    vy
    cA
    rexnal
    syl6ib
    com12
    expimpd
    a1d
    com3r
    jaod
    mpi
    @12
    @21
    @12
    @11
    con0
    wcel
    @21
    @8
    @21
    vx
    @11
    con0
    @6
    @11
    wceq
    @7
    @20
    vy
    cA
    @6
    @11
    @5
    csdm
    breq2
    ralbidv
    elrab
    simprbi
    con3i
    syl56
    ralrimiv
    @9
    con0
    wss
    @10
    @14
    wa
    @15
    wi
    @8
    vx
    con0
    ssrab2
    vz
    @3
    @9
    oneqmini
    ax-mp
    syl2anc
end
