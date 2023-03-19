include "ctpos.mm"
include "cvv.mm"
include "cxp.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "cv.mm"
include "ccnv.mm"
include "cuni.mm"
include "cmpt.mm"
include "ccom.mm"
include "cdm.mm"
include "df-tpos.mm"
include "wss.mm"
include "cres.mm"
include "wceq.mm"
include "wrel.mm"
include "relcnv.mm"
include "df-rel.mm"
include "mpbi.mm"
include "unss1.mm"
include "resmpt.mm"
include "mp2b.mm"
include "resss.mm"
include "eqsstr3i.mm"
include "coss2.mm"
include "ax-mp.mm"
include "eqsstri.mm"
include "relco.mm"
include "cop.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "vex.mm"
include "opelco.mm"
include "eleq1.mm"
include "sneq.mm"
include "cnveqd.mm"
include "unieqd.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "df-mpt.mm"
include "brab.mm"
include "wi.mm"
include "simplr.mm"
include "breldm.mm"
include "adantl.mm"
include "eqeltrrd.mm"
include "wb.mm"
include "elvv.mm"
include "opswap.mm"
include "eleq1i.mm"
include "opelcnv.mm"
include "bitr4i.mm"
include "eleq1d.mm"
include "bibi12d.mm"
include "mpbiri.mm"
include "exlimivv.mm"
include "sylbi.mm"
include "biimpcd.mm"
include "elun1.mm"
include "syl6.mm"
include "syl.mm"
include "elun2.mm"
include "a1i.mm"
include "wo.mm"
include "simpll.mm"
include "elun.mm"
include "sylib.mm"
include "mpjaod.mm"
include "simpr.mm"
include "eqbrtrrd.mm"
include "jca.mm"
include "sylanb.mm"
include "brtpos2.mm"
include "sylibr.mm"
include "df-br.mm"
include "exlimiv.mm"
include "relssi.mm"
include "eqssi.mm"

theorem dftpos4
  let vx: setvar x
  let cF: class F
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vz: setvar z
  let cG: class G

  disjoint F x
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G x
  assert |- tpos F = ( F o. ( x e. ( ( _V X. _V ) u. { (/) } ) |-> U. `' { x } ) )

  proof
    cF
    ctpos
    #
    cF
    vx
    cvv
    cvv
    cxp
    #
    c0
    csn
    #
    cun
    #
    vx
    cv
    #
    csn
    #
    ccnv
    #
    cuni
    #
    cmpt
    #
    ccom
    #
    @0
    cF
    vx
    cF
    cdm
    #
    ccnv
    #
    @2
    cun
    #
    @7
    cmpt
    #
    ccom
    #
    @9
    vx
    cF
    df-tpos
    @13
    @8
    wss
    @14
    @9
    wss
    @13
    @8
    @12
    cres
    #
    @8
    @11
    @1
    wss
    #
    @12
    @3
    wss
    @15
    @13
    wceq
    @11
    wrel
    @16
    @10
    relcnv
    @11
    df-rel
    mpbi
    @11
    @1
    @2
    unss1
    vx
    @3
    @12
    @7
    resmpt
    mp2b
    @8
    @12
    resss
    eqsstr3i
    @13
    @8
    cF
    coss2
    ax-mp
    eqsstri
    vy
    vz
    @9
    @0
    cF
    @8
    relco
    vy
    cv
    #
    vz
    cv
    #
    cop
    #
    @9
    wcel
    @17
    vw
    cv
    #
    @8
    wbr
    #
    @20
    @18
    cF
    wbr
    #
    wa
    #
    vw
    wex
    @19
    @0
    wcel
    #
    vw
    @17
    @18
    cF
    @8
    vy
    vex
    #
    vz
    vex
    #
    opelco
    @23
    @24
    vw
    @23
    @17
    @18
    @0
    wbr
    #
    @24
    @23
    @17
    @12
    wcel
    #
    @17
    csn
    #
    ccnv
    #
    cuni
    #
    @18
    cF
    wbr
    #
    wa
    #
    @27
    @21
    @17
    @3
    wcel
    #
    @20
    @31
    wceq
    #
    wa
    #
    @22
    @33
    @4
    @3
    wcel
    #
    @18
    @7
    wceq
    #
    wa
    @34
    @18
    @31
    wceq
    #
    wa
    @36
    vx
    vz
    @17
    @20
    @8
    @25
    vw
    vex
    #
    @4
    @17
    wceq
    #
    @37
    @34
    @38
    @39
    @4
    @17
    @3
    eleq1
    @41
    @7
    @31
    @18
    @41
    @6
    @30
    @41
    @5
    @29
    @4
    @17
    sneq
    cnveqd
    unieqd
    eqeq2d
    anbi12d
    @18
    @20
    wceq
    @39
    @35
    @34
    @18
    @20
    @31
    eqeq1
    anbi2d
    vx
    vz
    @3
    @7
    df-mpt
    brab
    @36
    @22
    wa
    #
    @28
    @32
    @42
    @17
    @1
    wcel
    #
    @28
    @17
    @2
    wcel
    #
    @42
    @31
    @10
    wcel
    #
    @43
    @28
    wi
    @42
    @20
    @31
    @10
    @34
    @35
    @22
    simplr
    #
    @22
    @20
    @10
    wcel
    @36
    @20
    @18
    cF
    @40
    @26
    breldm
    adantl
    eqeltrrd
    @45
    @43
    @17
    @11
    wcel
    #
    @28
    @43
    @45
    @47
    @43
    @17
    @18
    @20
    cop
    #
    wceq
    #
    vw
    wex
    vz
    wex
    @45
    @47
    wb
    #
    vz
    vw
    @17
    elvv
    @49
    @50
    vz
    vw
    @49
    @50
    @48
    csn
    #
    ccnv
    #
    cuni
    #
    @10
    wcel
    #
    @48
    @11
    wcel
    #
    wb
    @54
    @20
    @18
    cop
    #
    @10
    wcel
    @55
    @53
    @56
    @10
    @18
    @20
    opswap
    eleq1i
    @18
    @20
    @10
    @26
    @40
    opelcnv
    bitr4i
    @49
    @45
    @54
    @47
    @55
    @49
    @31
    @53
    @10
    @49
    @30
    @52
    @49
    @29
    @51
    @17
    @48
    sneq
    cnveqd
    unieqd
    eleq1d
    @17
    @48
    @11
    eleq1
    bibi12d
    mpbiri
    exlimivv
    sylbi
    biimpcd
    @17
    @11
    @2
    elun1
    syl6
    syl
    @44
    @28
    wi
    @42
    @17
    @2
    @11
    elun2
    a1i
    @42
    @34
    @43
    @44
    wo
    @34
    @35
    @22
    simpll
    @17
    @1
    @2
    elun
    sylib
    mpjaod
    @42
    @20
    @31
    @18
    cF
    @46
    @36
    @22
    simpr
    eqbrtrrd
    jca
    sylanb
    @18
    cvv
    wcel
    @27
    @33
    wb
    @26
    @17
    @18
    cF
    cvv
    brtpos2
    ax-mp
    sylibr
    @17
    @18
    @0
    df-br
    sylib
    exlimiv
    sylbi
    relssi
    eqssi
end
