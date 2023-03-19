include "cc.mm"
include "wf.mm"
include "cibl.mm"
include "wcel.mm"
include "cre.mm"
include "cim.mm"
include "cpr.mm"
include "cr.mm"
include "cv.mm"
include "cfv.mm"
include "cabs.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "citg2.mm"
include "wa.mm"
include "wceq.mm"
include "wo.mm"
include "elpri.mm"
include "fveq1.mm"
include "fveq2d.mm"
include "ifeq1d.mm"
include "mpteq2dv.mm"
include "adantl.mm"
include "cmbf.mm"
include "ffvelrn.mm"
include "recld.mm"
include "adantlr.mm"
include "simpl.mm"
include "feqmptd.mm"
include "simpr.mm"
include "eqeltrrd.mm"
include "iblcn.mm"
include "biimpa.mm"
include "syldan.mm"
include "simpld.mm"
include "ccom.mm"
include "recnd.mm"
include "eqidd.mm"
include "absf.mm"
include "a1i.mm"
include "fveq2.mm"
include "fmptco.mm"
include "adantr.mm"
include "eqid.mm"
include "fmptd.mm"
include "iblmbf.mm"
include "ismbfcn2.mm"
include "ftc1anclem1.mm"
include "syl2anc.mm"
include "iblabsnc.mm"
include "wb.mm"
include "abscld.mm"
include "absge0d.mm"
include "iblpos.mm"
include "mpbid.mm"
include "simprd.mm"
include "eqeltrd.mm"
include "imcld.mm"
include "jaodan.mm"
include "sylan2.mm"
include "3impa.mm"

theorem ftc1anclem2
  let vt: setvar t
  let cA: class A
  let cF: class F
  let cG: class G
  let vx: setvar x

  disjoint F t
  disjoint A t
  disjoint G t
  disjoint t x
  disjoint F x
  disjoint A x
  disjoint G x
  assert |- ( ( F : A --> CC /\ F e. L^1 /\ G e. { Re , Im } ) -> ( S.2 ` ( t e. RR |-> if ( t e. A , ( abs ` ( G ` ( F ` t ) ) ) , 0 ) ) ) e. RR )

  proof
    cA
    cc
    cF
    wf
    #
    cF
    cibl
    wcel
    #
    cG
    cre
    cim
    cpr
    wcel
    #
    vt
    cr
    vt
    cv
    #
    cA
    wcel
    #
    @3
    cF
    cfv
    #
    cG
    cfv
    #
    cabs
    cfv
    #
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cr
    wcel
    #
    @2
    @0
    @1
    wa
    #
    cG
    cre
    wceq
    #
    cG
    cim
    wceq
    #
    wo
    @11
    cG
    cre
    cim
    elpri
    @12
    @13
    @11
    @14
    @12
    @13
    wa
    @10
    vt
    cr
    @4
    @5
    cre
    cfv
    #
    cabs
    cfv
    #
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cr
    @13
    @10
    @19
    wceq
    @12
    @13
    @9
    @18
    citg2
    @13
    vt
    cr
    @8
    @17
    @13
    @4
    @7
    @16
    cc0
    @13
    @6
    @15
    cabs
    @5
    cG
    cre
    fveq1
    fveq2d
    ifeq1d
    mpteq2dv
    fveq2d
    adantl
    @12
    @19
    cr
    wcel
    #
    @13
    @12
    vt
    cA
    @16
    cmpt
    #
    cmbf
    wcel
    #
    @20
    @12
    @21
    cibl
    wcel
    #
    @22
    @20
    wa
    #
    @12
    vt
    cA
    @15
    cr
    @0
    @4
    @15
    cr
    wcel
    @1
    @0
    @4
    wa
    #
    @5
    cA
    cc
    @3
    cF
    ffvelrn
    #
    recld
    #
    adantlr
    @12
    vt
    cA
    @15
    cmpt
    #
    cibl
    wcel
    #
    vt
    cA
    @5
    cim
    cfv
    #
    cmpt
    #
    cibl
    wcel
    #
    @0
    @1
    vt
    cA
    @5
    cmpt
    #
    cibl
    wcel
    #
    @29
    @32
    wa
    #
    @12
    cF
    @33
    cibl
    @12
    vt
    cA
    cc
    cF
    @0
    @1
    simpl
    feqmptd
    #
    @0
    @1
    simpr
    eqeltrrd
    @0
    @34
    @35
    @0
    vt
    cA
    @5
    @26
    iblcn
    biimpa
    syldan
    #
    simpld
    @12
    cabs
    @28
    ccom
    #
    @21
    cmbf
    @0
    @38
    @21
    wceq
    @1
    @0
    vt
    vx
    cA
    cc
    @15
    vx
    cv
    #
    cabs
    cfv
    #
    @16
    @28
    cabs
    @25
    @15
    @27
    recnd
    #
    @0
    @28
    eqidd
    @0
    vx
    cc
    cr
    cabs
    cc
    cr
    cabs
    wf
    @0
    absf
    a1i
    feqmptd
    #
    @39
    @15
    cabs
    fveq2
    fmptco
    adantr
    @12
    cA
    cr
    @28
    wf
    #
    @28
    cmbf
    wcel
    #
    @38
    cmbf
    wcel
    @0
    @43
    @1
    @0
    vt
    cA
    @15
    cr
    @28
    @27
    @28
    eqid
    fmptd
    adantr
    @12
    @44
    @31
    cmbf
    wcel
    #
    @0
    @1
    @33
    cmbf
    wcel
    #
    @44
    @45
    wa
    #
    @12
    cF
    @33
    cmbf
    @36
    @1
    cF
    cmbf
    wcel
    @0
    cF
    iblmbf
    adantl
    eqeltrrd
    @0
    @46
    @47
    @0
    vt
    cA
    @5
    @26
    ismbfcn2
    biimpa
    syldan
    #
    simpld
    cA
    @28
    ftc1anclem1
    syl2anc
    eqeltrrd
    iblabsnc
    @0
    @23
    @24
    wb
    @1
    @0
    vt
    cA
    @16
    @25
    @15
    @41
    abscld
    @25
    @15
    @41
    absge0d
    iblpos
    adantr
    mpbid
    simprd
    adantr
    eqeltrd
    @12
    @14
    wa
    @10
    vt
    cr
    @4
    @30
    cabs
    cfv
    #
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cr
    @14
    @10
    @52
    wceq
    @12
    @14
    @9
    @51
    citg2
    @14
    vt
    cr
    @8
    @50
    @14
    @4
    @7
    @49
    cc0
    @14
    @6
    @30
    cabs
    @5
    cG
    cim
    fveq1
    fveq2d
    ifeq1d
    mpteq2dv
    fveq2d
    adantl
    @12
    @52
    cr
    wcel
    #
    @14
    @12
    vt
    cA
    @49
    cmpt
    #
    cmbf
    wcel
    #
    @53
    @12
    @54
    cibl
    wcel
    #
    @55
    @53
    wa
    #
    @12
    vt
    cA
    @30
    cc
    @0
    @4
    @30
    cc
    wcel
    @1
    @25
    @30
    @25
    @5
    @26
    imcld
    #
    recnd
    #
    adantlr
    @12
    @29
    @32
    @37
    simprd
    @12
    cabs
    @31
    ccom
    #
    @54
    cmbf
    @0
    @60
    @54
    wceq
    @1
    @0
    vt
    vx
    cA
    cc
    @30
    @40
    @49
    @31
    cabs
    @59
    @0
    @31
    eqidd
    @42
    @39
    @30
    cabs
    fveq2
    fmptco
    adantr
    @12
    cA
    cr
    @31
    wf
    #
    @45
    @60
    cmbf
    wcel
    @0
    @61
    @1
    @0
    vt
    cA
    @30
    cr
    @31
    @58
    @31
    eqid
    fmptd
    adantr
    @12
    @44
    @45
    @48
    simprd
    cA
    @31
    ftc1anclem1
    syl2anc
    eqeltrrd
    iblabsnc
    @0
    @56
    @57
    wb
    @1
    @0
    vt
    cA
    @49
    @25
    @30
    @59
    abscld
    @25
    @30
    @59
    absge0d
    iblpos
    adantr
    mpbid
    simprd
    adantr
    eqeltrd
    jaodan
    sylan2
    3impa
end
