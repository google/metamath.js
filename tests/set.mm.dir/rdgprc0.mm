include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "c0.mm"
include "crdg.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "cdm.mm"
include "wlim.mm"
include "crn.mm"
include "cuni.mm"
include "cif.mm"
include "cmpt.mm"
include "cres.mm"
include "con0.mm"
include "0elon.mm"
include "rdgval.mm"
include "ax-mp.mm"
include "res0.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "wa.mm"
include "eqeq1.mm"
include "wb.mm"
include "dmeq.mm"
include "limeq.mm"
include "syl.mm"
include "rneq.mm"
include "unieqd.mm"
include "id.mm"
include "fveq12d.mm"
include "fveq2d.mm"
include "ifbieq12d.mm"
include "ifbieq2d.mm"
include "eleq1d.mm"
include "eqid.mm"
include "dmmpt.mm"
include "elrab2.mm"
include "iftruei.mm"
include "eleq1i.mm"
include "biimpi.mm"
include "adantl.mm"
include "sylbi.mm"
include "con3i.mm"
include "ndmfv.mm"
include "syl5eq.mm"

theorem rdgprc0
  let cF: class F
  let cI: class I
  let vg: setvar g


  assert |- ( -. I e. _V -> ( rec ( F , I ) ` (/) ) = (/) )

  proof
    cI
    cvv
    wcel
    #
    wn
    #
    c0
    cF
    cI
    crdg
    #
    cfv
    #
    c0
    vg
    cvv
    vg
    cv
    #
    c0
    wceq
    #
    cI
    @4
    cdm
    #
    wlim
    #
    @4
    crn
    #
    cuni
    #
    @6
    cuni
    #
    @4
    cfv
    #
    cF
    cfv
    #
    cif
    #
    cif
    #
    cmpt
    #
    cfv
    #
    c0
    @3
    @2
    c0
    cres
    #
    @15
    cfv
    #
    @16
    c0
    con0
    wcel
    @3
    @18
    wceq
    0elon
    cI
    c0
    vg
    cF
    rdgval
    ax-mp
    @17
    c0
    @15
    @2
    res0
    fveq2i
    eqtri
    @1
    c0
    @15
    cdm
    #
    wcel
    #
    wn
    @16
    c0
    wceq
    @20
    @0
    @20
    c0
    cvv
    wcel
    #
    c0
    c0
    wceq
    #
    cI
    c0
    cdm
    #
    wlim
    #
    c0
    crn
    #
    cuni
    #
    @23
    cuni
    #
    c0
    cfv
    #
    cF
    cfv
    #
    cif
    #
    cif
    #
    cvv
    wcel
    #
    wa
    @0
    @14
    cvv
    wcel
    @32
    vg
    c0
    cvv
    @19
    @5
    @14
    @31
    cvv
    @5
    @5
    @22
    @13
    @30
    cI
    @4
    c0
    c0
    eqeq1
    @5
    @7
    @24
    @9
    @12
    @26
    @29
    @5
    @6
    @23
    wceq
    @7
    @24
    wb
    @4
    c0
    dmeq
    #
    @6
    @23
    limeq
    syl
    @5
    @8
    @25
    @4
    c0
    rneq
    unieqd
    @5
    @11
    @28
    cF
    @5
    @10
    @27
    @4
    c0
    @5
    id
    @5
    @6
    @23
    @33
    unieqd
    fveq12d
    fveq2d
    ifbieq12d
    ifbieq2d
    eleq1d
    vg
    cvv
    @14
    @15
    @15
    eqid
    dmmpt
    elrab2
    @32
    @0
    @21
    @32
    @0
    @31
    cI
    cvv
    @22
    cI
    @30
    c0
    eqid
    iftruei
    eleq1i
    biimpi
    adantl
    sylbi
    con3i
    c0
    @15
    ndmfv
    syl
    syl5eq
end
