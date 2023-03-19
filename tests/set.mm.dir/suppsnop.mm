include "wcel.mm"
include "w3a.mm"
include "csupp.mm"
include "co.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "wne.mm"
include "cdm.mm"
include "crab.mm"
include "c0.mm"
include "cif.mm"
include "wceq.mm"
include "cvv.mm"
include "wf.mm"
include "cop.mm"
include "wa.mm"
include "wf1o.mm"
include "f1osng.mm"
include "f1of.mm"
include "syl.mm"
include "3adant3.mm"
include "feq1i.mm"
include "sylibr.mm"
include "snex.mm"
include "a1i.mm"
include "fex.mm"
include "syl2anc.mm"
include "simp3.mm"
include "suppval.mm"
include "dmeqd.mm"
include "dmsnopg.mm"
include "3ad2ant2.mm"
include "eqtrd.mm"
include "rabeq.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "neeq1d.mm"
include "rabsnif.mm"
include "syl6eq.mm"
include "wn.mm"
include "cfv.mm"
include "wfn.mm"
include "fnsng.mm"
include "eqcomi.mm"
include "fneq1d.mm"
include "mpbid.mm"
include "snidg.mm"
include "3ad2ant1.mm"
include "fnsnfv.mm"
include "eqcomd.mm"
include "fveq1i.mm"
include "fvsng.mm"
include "syl5eq.mm"
include "sneqd.mm"
include "wb.mm"
include "sneqbg.mm"
include "necon3abid.mm"
include "3bitrd.mm"
include "ifbid.mm"
include "ifnot.mm"
include "3eqtrd.mm"

theorem suppsnop
  let cU: class U
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  assume suppsnop.f: |- F = { <. X , Y >. }


  assert |- ( ( X e. V /\ Y e. W /\ Z e. U ) -> ( F supp Z ) = if ( Y = Z , (/) , { X } ) )

  proof
    cX
    cV
    wcel
    #
    cY
    cW
    wcel
    #
    cZ
    cU
    wcel
    #
    w3a
    #
    cF
    cZ
    csupp
    co
    #
    cF
    vx
    cv
    #
    csn
    #
    cima
    #
    cZ
    csn
    #
    wne
    #
    vx
    cF
    cdm
    #
    crab
    #
    cF
    cX
    csn
    #
    cima
    #
    @8
    wne
    #
    @12
    c0
    cif
    #
    cY
    cZ
    wceq
    #
    c0
    @12
    cif
    #
    @3
    cF
    cvv
    wcel
    #
    @2
    @4
    @11
    wceq
    @3
    @12
    cY
    csn
    #
    cF
    wf
    #
    @12
    cvv
    wcel
    #
    @18
    @3
    @12
    @19
    cX
    cY
    cop
    csn
    #
    wf
    #
    @20
    @0
    @1
    @23
    @2
    @0
    @1
    wa
    @12
    @19
    @22
    wf1o
    @23
    cX
    cY
    cV
    cW
    f1osng
    @12
    @19
    @22
    f1of
    syl
    3adant3
    @12
    @19
    cF
    @22
    suppsnop.f
    feq1i
    sylibr
    @21
    @3
    cX
    snex
    a1i
    @12
    @19
    cvv
    cF
    fex
    syl2anc
    @0
    @1
    @2
    simp3
    vx
    cvv
    cU
    cF
    cZ
    suppval
    syl2anc
    @3
    @11
    @9
    vx
    @12
    crab
    #
    @15
    @3
    @10
    @12
    wceq
    @11
    @24
    wceq
    @3
    @10
    @22
    cdm
    #
    @12
    @3
    cF
    @22
    cF
    @22
    wceq
    @3
    suppsnop.f
    a1i
    dmeqd
    @1
    @0
    @25
    @12
    wceq
    @2
    cX
    cY
    cW
    dmsnopg
    3ad2ant2
    eqtrd
    @9
    vx
    @10
    @12
    rabeq
    syl
    @9
    @14
    vx
    cX
    @5
    cX
    wceq
    #
    @7
    @13
    @8
    @26
    @6
    @12
    cF
    @5
    cX
    sneq
    imaeq2d
    neeq1d
    rabsnif
    syl6eq
    @3
    @15
    @16
    wn
    #
    @12
    c0
    cif
    @17
    @3
    @14
    @27
    @12
    c0
    @3
    @14
    cX
    cF
    cfv
    #
    csn
    #
    @8
    wne
    @19
    @8
    wne
    @27
    @3
    @13
    @29
    @8
    @3
    cF
    @12
    wfn
    #
    cX
    @12
    wcel
    #
    @13
    @29
    wceq
    @3
    @22
    @12
    wfn
    #
    @30
    @0
    @1
    @32
    @2
    cX
    cY
    cV
    cW
    fnsng
    3adant3
    @3
    @12
    @22
    cF
    @22
    cF
    wceq
    @3
    cF
    @22
    suppsnop.f
    eqcomi
    a1i
    fneq1d
    mpbid
    @0
    @1
    @31
    @2
    cX
    cV
    snidg
    3ad2ant1
    @30
    @31
    wa
    @29
    @13
    @12
    cX
    cF
    fnsnfv
    eqcomd
    syl2anc
    neeq1d
    @3
    @29
    @19
    @8
    @3
    @28
    cY
    @3
    @28
    cX
    @22
    cfv
    #
    cY
    cX
    cF
    @22
    suppsnop.f
    fveq1i
    @0
    @1
    @33
    cY
    wceq
    @2
    cX
    cY
    cV
    cW
    fvsng
    3adant3
    syl5eq
    sneqd
    neeq1d
    @3
    @16
    @19
    @8
    @1
    @0
    @19
    @8
    wceq
    @16
    wb
    @2
    cY
    cZ
    cW
    sneqbg
    3ad2ant2
    necon3abid
    3bitrd
    ifbid
    @16
    @12
    c0
    ifnot
    syl6eq
    3eqtrd
end
