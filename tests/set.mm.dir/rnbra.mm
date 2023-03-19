include "cbr.mm"
include "crn.mm"
include "clf.mm"
include "ccnfn.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cnmf.mm"
include "cfv.mm"
include "cr.mm"
include "lnfncnbd.mm"
include "pm5.32i.mm"
include "elin.mm"
include "wceq.mm"
include "chil.mm"
include "wrex.mm"
include "wfn.mm"
include "wb.mm"
include "csp.mm"
include "co.mm"
include "cmpt.mm"
include "ax-hilex.mm"
include "mptex.mm"
include "df-bra.mm"
include "fnmpti.mm"
include "fvelrnb.mm"
include "ax-mp.mm"
include "bralnfn.mm"
include "brabn.mm"
include "jca.mm"
include "eleq1.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "syl5ibcom.mm"
include "rexlimiv.mm"
include "wral.mm"
include "riesz1.mm"
include "biimpa.mm"
include "wi.mm"
include "braval.mm"
include "eqtr3.mm"
include "ex.mm"
include "syl.mm"
include "ralimdva.mm"
include "adantl.mm"
include "cc.mm"
include "wf.mm"
include "brafn.mm"
include "lnfnf.mm"
include "adantr.mm"
include "ffn.mm"
include "eqfnfv.mm"
include "syl2an.mm"
include "syl2anr.mm"
include "sylibrd.mm"
include "reximdva.mm"
include "mpd.mm"
include "impbii.mm"
include "bitri.mm"
include "3bitr4ri.mm"
include "eqriv.mm"

theorem rnbra
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let vt: setvar t
  let vu: setvar u
  let cT: class T
  let cU: class U


  assert |- ran bra = ( LinFn i^i ContFn )

  proof
    vt
    cbr
    crn
    #
    clf
    ccnfn
    cin
    #
    vt
    cv
    #
    clf
    wcel
    #
    @2
    ccnfn
    wcel
    #
    wa
    @3
    @2
    cnmf
    cfv
    #
    cr
    wcel
    #
    wa
    #
    @2
    @1
    wcel
    @2
    @0
    wcel
    #
    @3
    @4
    @6
    @2
    lnfncnbd
    pm5.32i
    @2
    clf
    ccnfn
    elin
    @8
    vx
    cv
    #
    cbr
    cfv
    #
    @2
    wceq
    #
    vx
    chil
    wrex
    #
    @7
    cbr
    chil
    wfn
    @8
    @12
    wb
    vx
    chil
    vy
    chil
    vy
    cv
    #
    @9
    csp
    co
    #
    cmpt
    cbr
    vy
    chil
    @14
    ax-hilex
    mptex
    vx
    vy
    df-bra
    fnmpti
    vx
    chil
    @2
    cbr
    fvelrnb
    ax-mp
    @12
    @7
    @11
    @7
    vx
    chil
    @9
    chil
    wcel
    #
    @10
    clf
    wcel
    #
    @10
    cnmf
    cfv
    #
    cr
    wcel
    #
    wa
    @11
    @7
    @15
    @16
    @18
    @9
    bralnfn
    @9
    brabn
    jca
    @11
    @16
    @3
    @18
    @6
    @10
    @2
    clf
    eleq1
    @11
    @17
    @5
    cr
    @10
    @2
    cnmf
    fveq2
    eleq1d
    anbi12d
    syl5ibcom
    rexlimiv
    @7
    @13
    @2
    cfv
    #
    @14
    wceq
    #
    vy
    chil
    wral
    #
    vx
    chil
    wrex
    #
    @12
    @3
    @6
    @22
    vy
    vx
    @2
    riesz1
    biimpa
    @7
    @21
    @11
    vx
    chil
    @7
    @15
    wa
    @21
    @13
    @10
    cfv
    #
    @19
    wceq
    #
    vy
    chil
    wral
    #
    @11
    @15
    @21
    @25
    wi
    @7
    @15
    @20
    @24
    vy
    chil
    @15
    @13
    chil
    wcel
    wa
    @23
    @14
    wceq
    #
    @20
    @24
    wi
    @9
    @13
    braval
    @26
    @20
    @24
    @23
    @19
    @14
    eqtr3
    ex
    syl
    ralimdva
    adantl
    @15
    chil
    cc
    @10
    wf
    #
    chil
    cc
    @2
    wf
    #
    @11
    @25
    wb
    #
    @7
    @9
    brafn
    @3
    @28
    @6
    @2
    lnfnf
    adantr
    @27
    @10
    chil
    wfn
    @2
    chil
    wfn
    @29
    @28
    chil
    cc
    @10
    ffn
    chil
    cc
    @2
    ffn
    vy
    chil
    @10
    @2
    eqfnfv
    syl2an
    syl2anr
    sylibrd
    reximdva
    mpd
    impbii
    bitri
    3bitr4ri
    eqriv
end
