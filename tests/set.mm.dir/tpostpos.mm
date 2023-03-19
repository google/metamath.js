include "ctpos.mm"
include "cvv.mm"
include "cxp.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "cin.mm"
include "reltpos.mm"
include "wss.mm"
include "wrel.mm"
include "inss2.mm"
include "relxp.mm"
include "relss.mm"
include "mp2.mm"
include "cv.mm"
include "cdm.mm"
include "ccnv.mm"
include "wcel.mm"
include "cuni.mm"
include "wbr.mm"
include "wa.mm"
include "wo.mm"
include "relcnv.mm"
include "df-rel.mm"
include "mpbi.mm"
include "simpl.mm"
include "sseldi.mm"
include "simpr.mm"
include "cop.mm"
include "wceq.mm"
include "wex.mm"
include "wb.mm"
include "elvv.mm"
include "eleq1.mm"
include "vex.mm"
include "opelcnv.mm"
include "syl6bb.mm"
include "sneq.mm"
include "cnveqd.mm"
include "unieqd.mm"
include "opswap.mm"
include "syl6eq.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "opex.mm"
include "breldm.mm"
include "pm4.71ri.mm"
include "brtpos.mm"
include "ax-mp.mm"
include "bitr3i.mm"
include "breq1.mm"
include "bitr4d.mm"
include "exlimivv.mm"
include "sylbi.mm"
include "iba.mm"
include "bitrd.mm"
include "pm5.21nii.mm"
include "elsni.mm"
include "sneqd.mm"
include "cnvsn0.mm"
include "uni0.mm"
include "brtpos0.mm"
include "pm5.32i.mm"
include "ancom.mm"
include "bitri.mm"
include "orbi12i.mm"
include "andir.mm"
include "andi.mm"
include "3bitr4i.mm"
include "elun.mm"
include "anbi1i.mm"
include "brxp.mm"
include "mpbiran2.mm"
include "anbi2i.mm"
include "brtpos2.mm"
include "brin.mm"
include "eqbrriv.mm"

theorem tpostpos
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vz: setvar z
  let cG: class G


  assert |- tpos tpos F = ( F i^i ( ( ( _V X. _V ) u. { (/) } ) X. _V ) )

  proof
    vw
    vz
    cF
    ctpos
    #
    ctpos
    #
    cF
    cvv
    cvv
    cxp
    #
    c0
    csn
    #
    cun
    #
    cvv
    cxp
    #
    cin
    #
    @0
    reltpos
    @6
    @5
    wss
    @5
    wrel
    @6
    wrel
    cF
    @5
    inss2
    @4
    cvv
    relxp
    @6
    @5
    relss
    mp2
    vw
    cv
    #
    @0
    cdm
    #
    ccnv
    #
    @3
    cun
    wcel
    #
    @7
    csn
    #
    ccnv
    #
    cuni
    #
    vz
    cv
    #
    @0
    wbr
    #
    wa
    #
    @7
    @14
    cF
    wbr
    #
    @7
    @14
    @5
    wbr
    #
    wa
    #
    @7
    @14
    @1
    wbr
    #
    @7
    @14
    @6
    wbr
    @7
    @9
    wcel
    #
    @7
    @3
    wcel
    #
    wo
    #
    @15
    wa
    #
    @17
    @7
    @2
    wcel
    #
    @22
    wo
    #
    wa
    #
    @16
    @19
    @21
    @15
    wa
    #
    @22
    @15
    wa
    #
    wo
    @17
    @25
    wa
    #
    @17
    @22
    wa
    #
    wo
    @24
    @27
    @28
    @30
    @29
    @31
    @28
    @25
    @30
    @28
    @9
    @2
    @7
    @9
    wrel
    @9
    @2
    wss
    @8
    relcnv
    @9
    df-rel
    mpbi
    @21
    @15
    simpl
    sseldi
    @17
    @25
    simpr
    @25
    @28
    @17
    @30
    @25
    @7
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    vy
    wex
    vx
    wex
    @28
    @17
    wb
    #
    vx
    vy
    @7
    elvv
    @35
    @36
    vx
    vy
    @35
    @28
    @34
    @14
    cF
    wbr
    #
    @17
    @35
    @28
    @33
    @32
    cop
    #
    @8
    wcel
    #
    @38
    @14
    @0
    wbr
    #
    wa
    #
    @37
    @35
    @21
    @39
    @15
    @40
    @35
    @21
    @34
    @9
    wcel
    @39
    @7
    @34
    @9
    eleq1
    @32
    @33
    @8
    vx
    vex
    vy
    vex
    opelcnv
    syl6bb
    @35
    @13
    @38
    @14
    @0
    @35
    @13
    @34
    csn
    #
    ccnv
    #
    cuni
    @38
    @35
    @12
    @43
    @35
    @11
    @42
    @7
    @34
    sneq
    cnveqd
    unieqd
    @32
    @33
    opswap
    syl6eq
    breq1d
    anbi12d
    @41
    @40
    @37
    @40
    @39
    @38
    @14
    @0
    @33
    @32
    opex
    vz
    vex
    #
    breldm
    pm4.71ri
    @14
    cvv
    wcel
    #
    @40
    @37
    wb
    @44
    @33
    @32
    @14
    cF
    cvv
    brtpos
    ax-mp
    bitr3i
    syl6bb
    @7
    @34
    @14
    cF
    breq1
    bitr4d
    exlimivv
    sylbi
    @25
    @17
    iba
    bitrd
    pm5.21nii
    @29
    @22
    @17
    wa
    @31
    @22
    @15
    @17
    @22
    @15
    c0
    @14
    cF
    wbr
    #
    @17
    @22
    @15
    c0
    @14
    @0
    wbr
    #
    @46
    @22
    @13
    c0
    @14
    @0
    @22
    @13
    c0
    cuni
    c0
    @22
    @12
    c0
    @22
    @12
    @3
    ccnv
    c0
    @22
    @11
    @3
    @22
    @7
    c0
    @7
    c0
    elsni
    #
    sneqd
    cnveqd
    cnvsn0
    syl6eq
    unieqd
    uni0
    syl6eq
    breq1d
    @45
    @47
    @46
    wb
    @44
    @14
    cF
    cvv
    brtpos0
    ax-mp
    syl6bb
    @22
    @7
    c0
    @14
    cF
    @48
    breq1d
    bitr4d
    pm5.32i
    @22
    @17
    ancom
    bitri
    orbi12i
    @21
    @22
    @15
    andir
    @17
    @25
    @22
    andi
    3bitr4i
    @10
    @23
    @15
    @7
    @9
    @3
    elun
    anbi1i
    @18
    @26
    @17
    @18
    @7
    @4
    wcel
    #
    @26
    @18
    @49
    @45
    @44
    @7
    @14
    @4
    cvv
    brxp
    mpbiran2
    @7
    @2
    @3
    elun
    bitri
    anbi2i
    3bitr4i
    @45
    @20
    @16
    wb
    @44
    @7
    @14
    @0
    cvv
    brtpos2
    ax-mp
    @7
    @14
    cF
    @5
    brin
    3bitr4i
    eqbrriv
end
