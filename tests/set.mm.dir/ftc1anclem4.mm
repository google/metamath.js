include "citg1.mm"
include "cdm.mm"
include "wcel.mm"
include "cibl.mm"
include "cr.mm"
include "wf.mm"
include "w3a.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "cabs.mm"
include "cmpt.mm"
include "caddc.mm"
include "citg2.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cxr.mm"
include "cc.mm"
include "ffvelrn.mm"
include "recnd.mm"
include "i1ff.mm"
include "ffvelrnda.mm"
include "subcl.mm"
include "syl2anr.mm"
include "anandirs.mm"
include "abscld.mm"
include "rexrd.mm"
include "absge0d.mm"
include "elxrge0.mm"
include "sylanbrc.mm"
include "eqid.mm"
include "fmptd.mm"
include "3adant2.mm"
include "cof.mm"
include "cvv.mm"
include "reex.mm"
include "a1i.mm"
include "fvexd.mm"
include "eqidd.mm"
include "offval2.mm"
include "fveq2d.mm"
include "cmbf.mm"
include "ccom.mm"
include "wceq.mm"
include "id.mm"
include "feqmptd.mm"
include "absf.mm"
include "fveq2.mm"
include "fmptco.mm"
include "adantl.mm"
include "iblmbf.mm"
include "ftc1anclem1.mm"
include "sylan2.mm"
include "ancoms.mm"
include "eqeltrrd.mm"
include "3adant1.mm"
include "cico.mm"
include "elrege0.mm"
include "3ad2ant3.mm"
include "cif.mm"
include "iftrue.mm"
include "mpteq2ia.mm"
include "fveq2i.mm"
include "adantll.mm"
include "simpr.mm"
include "simpl.mm"
include "iblabsnc.mm"
include "iblpos.mm"
include "mpbid.mm"
include "simprd.mm"
include "syl5eqelr.mm"
include "3ad2ant1.mm"
include "i1fibl.mm"
include "i1fmbf.mm"
include "syl2anc.mm"
include "itg2addnc.mm"
include "eqtr3d.mm"
include "readdcld.mm"
include "eqeltrd.mm"
include "cofr.mm"
include "readdcl.mm"
include "adantlr.mm"
include "addge0d.mm"
include "wral.mm"
include "abs2dif2.mm"
include "ralrimiva.mm"
include "ofrfval2.mm"
include "mpbird.mm"
include "itg2le.mm"
include "syl3anc.mm"
include "itg2lecl.mm"

theorem ftc1anclem4
  let vt: setvar t
  let cF: class F
  let cG: class G
  let vx: setvar x

  disjoint F t
  disjoint G t
  disjoint t x
  disjoint F x
  disjoint G x
  assert |- ( ( F e. dom S.1 /\ G e. L^1 /\ G : RR --> RR ) -> ( S.2 ` ( t e. RR |-> ( abs ` ( ( G ` t ) - ( F ` t ) ) ) ) ) e. RR )

  proof
    cF
    citg1
    cdm
    wcel
    #
    cG
    cibl
    wcel
    #
    cr
    cr
    cG
    wf
    #
    w3a
    #
    cr
    cc0
    cpnf
    cicc
    co
    #
    vt
    cr
    vt
    cv
    #
    cG
    cfv
    #
    @5
    cF
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cmpt
    #
    wf
    #
    vt
    cr
    @6
    cabs
    cfv
    #
    @7
    cabs
    cfv
    #
    caddc
    co
    #
    cmpt
    #
    citg2
    cfv
    #
    cr
    wcel
    @10
    citg2
    cfv
    #
    @16
    cle
    wbr
    #
    @17
    cr
    wcel
    @0
    @2
    @11
    @1
    @0
    @2
    wa
    #
    vt
    cr
    @9
    @4
    @10
    @19
    @5
    cr
    wcel
    #
    wa
    #
    @9
    cxr
    wcel
    cc0
    @9
    cle
    wbr
    @9
    @4
    wcel
    @21
    @9
    @21
    @8
    @0
    @2
    @20
    @8
    cc
    wcel
    #
    @2
    @20
    wa
    #
    @6
    cc
    wcel
    #
    @7
    cc
    wcel
    #
    @22
    @0
    @20
    wa
    #
    @23
    @6
    cr
    cr
    @5
    cG
    ffvelrn
    #
    recnd
    #
    @26
    @7
    @0
    cr
    cr
    @5
    cF
    cF
    i1ff
    #
    ffvelrnda
    #
    recnd
    #
    @6
    @7
    subcl
    syl2anr
    anandirs
    #
    abscld
    #
    rexrd
    @21
    @8
    @32
    absge0d
    @9
    elxrge0
    sylanbrc
    @10
    eqid
    fmptd
    3adant2
    #
    @3
    @16
    vt
    cr
    @12
    cmpt
    #
    citg2
    cfv
    #
    vt
    cr
    @13
    cmpt
    #
    citg2
    cfv
    #
    caddc
    co
    #
    cr
    @3
    @35
    @37
    caddc
    cof
    co
    #
    citg2
    cfv
    @16
    @39
    @3
    @40
    @15
    citg2
    @3
    vt
    cr
    @12
    @13
    caddc
    @35
    @37
    cvv
    cvv
    cvv
    cr
    cvv
    wcel
    #
    @3
    reex
    a1i
    @3
    @20
    wa
    #
    @6
    cabs
    fvexd
    @42
    @7
    cabs
    fvexd
    @3
    @35
    eqidd
    @3
    @37
    eqidd
    offval2
    fveq2d
    @3
    @35
    @37
    @1
    @2
    @35
    cmbf
    wcel
    #
    @0
    @1
    @2
    wa
    #
    cabs
    cG
    ccom
    #
    @35
    cmbf
    @2
    @45
    @35
    wceq
    @1
    @2
    vt
    vx
    cr
    cc
    @6
    vx
    cv
    #
    cabs
    cfv
    #
    @12
    cG
    cabs
    @28
    @2
    vt
    cr
    cr
    cG
    @2
    id
    feqmptd
    @2
    vx
    cc
    cr
    cabs
    cc
    cr
    cabs
    wf
    #
    @2
    absf
    a1i
    feqmptd
    @46
    @6
    cabs
    fveq2
    fmptco
    adantl
    @2
    @1
    @45
    cmbf
    wcel
    #
    @1
    @2
    cG
    cmbf
    wcel
    @49
    cG
    iblmbf
    cr
    cG
    ftc1anclem1
    sylan2
    ancoms
    eqeltrrd
    #
    3adant1
    @2
    @0
    cr
    cc0
    cpnf
    cico
    co
    #
    @35
    wf
    @1
    @2
    vt
    cr
    @12
    @51
    @35
    @23
    @12
    cr
    wcel
    #
    cc0
    @12
    cle
    wbr
    #
    @12
    @51
    wcel
    @23
    @6
    @28
    abscld
    #
    @23
    @6
    @28
    absge0d
    #
    @12
    elrege0
    sylanbrc
    @35
    eqid
    fmptd
    3ad2ant3
    @1
    @2
    @36
    cr
    wcel
    @0
    @44
    @36
    vt
    cr
    @20
    @12
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cr
    @57
    @35
    citg2
    vt
    cr
    @56
    @12
    @20
    @12
    cc0
    iftrue
    mpteq2ia
    fveq2i
    @44
    @43
    @58
    cr
    wcel
    #
    @44
    @35
    cibl
    wcel
    @43
    @59
    wa
    @44
    vt
    cr
    @6
    cr
    @2
    @20
    @6
    cr
    wcel
    @1
    @27
    adantll
    @44
    cG
    vt
    cr
    @6
    cmpt
    cibl
    @44
    vt
    cr
    cr
    cG
    @1
    @2
    simpr
    feqmptd
    @1
    @2
    simpl
    eqeltrrd
    @50
    iblabsnc
    @44
    vt
    cr
    @12
    @2
    @20
    @52
    @1
    @54
    adantll
    @2
    @20
    @53
    @1
    @55
    adantll
    iblpos
    mpbid
    simprd
    syl5eqelr
    3adant1
    #
    @0
    @1
    cr
    @51
    @37
    wf
    @2
    @0
    vt
    cr
    @13
    @51
    @37
    @26
    @13
    cr
    wcel
    #
    cc0
    @13
    cle
    wbr
    #
    @13
    @51
    wcel
    @26
    @7
    @31
    abscld
    #
    @26
    @7
    @31
    absge0d
    #
    @13
    elrege0
    sylanbrc
    @37
    eqid
    fmptd
    3ad2ant1
    @0
    @1
    @38
    cr
    wcel
    @2
    @0
    @38
    vt
    cr
    @20
    @13
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cr
    @66
    @37
    citg2
    vt
    cr
    @65
    @13
    @20
    @13
    cc0
    iftrue
    mpteq2ia
    fveq2i
    @0
    @37
    cmbf
    wcel
    #
    @67
    cr
    wcel
    #
    @0
    @37
    cibl
    wcel
    @68
    @69
    wa
    @0
    vt
    cr
    @7
    cr
    @30
    @0
    cF
    vt
    cr
    @7
    cmpt
    cibl
    @0
    vt
    cr
    cr
    cF
    @29
    feqmptd
    #
    cF
    i1fibl
    eqeltrrd
    @0
    cabs
    cF
    ccom
    #
    @37
    cmbf
    @0
    vt
    vx
    cr
    cc
    @7
    @47
    @13
    cF
    cabs
    @31
    @70
    @0
    vx
    cc
    cr
    cabs
    @48
    @0
    absf
    a1i
    feqmptd
    @46
    @7
    cabs
    fveq2
    fmptco
    @0
    cr
    cr
    cF
    wf
    cF
    cmbf
    wcel
    @71
    cmbf
    wcel
    @29
    cF
    i1fmbf
    cr
    cF
    ftc1anclem1
    syl2anc
    eqeltrrd
    iblabsnc
    @0
    vt
    cr
    @13
    @63
    @64
    iblpos
    mpbid
    simprd
    syl5eqelr
    3ad2ant1
    #
    itg2addnc
    eqtr3d
    @3
    @36
    @38
    @60
    @72
    readdcld
    eqeltrd
    @3
    @11
    cr
    @4
    @15
    wf
    #
    @10
    @15
    cle
    cofr
    wbr
    #
    @18
    @34
    @0
    @2
    @73
    @1
    @19
    vt
    cr
    @14
    @4
    @15
    @21
    @14
    cxr
    wcel
    cc0
    @14
    cle
    wbr
    @14
    @4
    wcel
    @21
    @14
    @0
    @2
    @20
    @14
    cr
    wcel
    #
    @23
    @52
    @61
    @75
    @26
    @54
    @63
    @12
    @13
    readdcl
    syl2anr
    anandirs
    #
    rexrd
    @21
    @12
    @13
    @2
    @20
    @52
    @0
    @54
    adantll
    @0
    @20
    @61
    @2
    @63
    adantlr
    @2
    @20
    @53
    @0
    @55
    adantll
    @0
    @20
    @62
    @2
    @64
    adantlr
    addge0d
    @14
    elxrge0
    sylanbrc
    @15
    eqid
    fmptd
    3adant2
    @0
    @2
    @74
    @1
    @19
    @74
    @9
    @14
    cle
    wbr
    #
    vt
    cr
    wral
    @19
    @77
    vt
    cr
    @0
    @2
    @20
    @77
    @23
    @24
    @25
    @77
    @26
    @28
    @31
    @6
    @7
    abs2dif2
    syl2anr
    anandirs
    ralrimiva
    @19
    vt
    cr
    @9
    @14
    cle
    @10
    @15
    cvv
    cr
    cr
    @41
    @19
    reex
    a1i
    @33
    @76
    @19
    @10
    eqidd
    @19
    @15
    eqidd
    ofrfval2
    mpbird
    3adant2
    @10
    @15
    itg2le
    syl3anc
    @16
    @10
    itg2lecl
    syl3anc
end
