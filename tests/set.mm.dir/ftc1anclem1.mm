include "cr.mm"
include "wf.mm"
include "cmbf.mm"
include "wcel.mm"
include "wa.mm"
include "cabs.mm"
include "ccom.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "wceq.mm"
include "cc.mm"
include "ffvelrn.mm"
include "recnd.mm"
include "id.mm"
include "feqmptd.mm"
include "absf.mm"
include "a1i.mm"
include "fveq2.mm"
include "fmptco.mm"
include "adantr.mm"
include "abscld.mm"
include "eqid.mm"
include "fmptd.mm"
include "cdm.mm"
include "cvol.mm"
include "fdm.mm"
include "mbfdm.mm"
include "adantl.mm"
include "eqeltrrd.mm"
include "ccnv.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cima.mm"
include "cmnf.mm"
include "cneg.mm"
include "cun.mm"
include "crab.mm"
include "wb.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wn.mm"
include "cxr.mm"
include "rexr.mm"
include "elioopnf.mm"
include "syl.mm"
include "biantrurd.mm"
include "bicomd.mm"
include "sylan9bbr.mm"
include "ltnle.mm"
include "ancoms.mm"
include "sylan.mm"
include "absle.mm"
include "renegcl.mm"
include "lenlt.mm"
include "syl2anr.mm"
include "rexrd.mm"
include "elioomnf.mm"
include "sylan9bb.mm"
include "notbid.mm"
include "bitrd.mm"
include "anbi12d.mm"
include "wo.mm"
include "elun.mm"
include "oran.mm"
include "bitri.mm"
include "syl6bbr.mm"
include "3bitrd.mm"
include "an32s.mm"
include "rabbidva.mm"
include "mptpreima.mm"
include "3eqtr4g.mm"
include "simpl.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "eqtr4d.mm"
include "imaundi.mm"
include "syl6eq.mm"
include "adantlr.mm"
include "mbfima.mm"
include "unmbl.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "abslt.mm"
include "jca.mm"
include "elioo5.mm"
include "3expa.mm"
include "3bitr4d.mm"
include "ismbf2d.mm"

theorem ftc1anclem1
  let cA: class A
  let cF: class F
  let vt: setvar t
  let vx: setvar x


  assert |- ( ( F : A --> RR /\ F e. MblFn ) -> ( abs o. F ) e. MblFn )

  proof
    cA
    cr
    cF
    wf
    #
    cF
    cmbf
    wcel
    #
    wa
    #
    cabs
    cF
    ccom
    #
    vt
    cA
    vt
    cv
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    cmpt
    #
    cmbf
    @0
    @3
    @7
    wceq
    @1
    @0
    vt
    vx
    cA
    cc
    @5
    vx
    cv
    #
    cabs
    cfv
    @6
    cF
    cabs
    @0
    @4
    cA
    wcel
    #
    wa
    #
    @5
    cA
    cr
    @4
    cF
    ffvelrn
    #
    recnd
    #
    @0
    vt
    cA
    cr
    cF
    @0
    id
    feqmptd
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
    @8
    @5
    cabs
    fveq2
    fmptco
    adantr
    @2
    vx
    cA
    @7
    @0
    cA
    cr
    @7
    wf
    @1
    @0
    vt
    cA
    @6
    cr
    @7
    @10
    @5
    @12
    abscld
    #
    @7
    eqid
    #
    fmptd
    adantr
    @2
    cF
    cdm
    #
    cA
    cvol
    cdm
    #
    @0
    @15
    cA
    wceq
    @1
    cA
    cr
    cF
    fdm
    adantr
    @1
    @15
    @16
    wcel
    @0
    cF
    mbfdm
    adantl
    eqeltrrd
    @2
    @8
    cr
    wcel
    #
    wa
    #
    @7
    ccnv
    #
    @8
    cpnf
    cioo
    co
    #
    cima
    #
    cF
    ccnv
    #
    cmnf
    @8
    cneg
    #
    cioo
    co
    #
    cima
    #
    @22
    @20
    cima
    #
    cun
    #
    @16
    @0
    @17
    @21
    @27
    wceq
    @1
    @0
    @17
    wa
    #
    @21
    @22
    @24
    @20
    cun
    #
    cima
    #
    @27
    @28
    @21
    vt
    cA
    @5
    cmpt
    #
    ccnv
    #
    @29
    cima
    #
    @30
    @28
    @6
    @20
    wcel
    #
    vt
    cA
    crab
    @5
    @29
    wcel
    #
    vt
    cA
    crab
    @21
    @33
    @28
    @34
    @35
    vt
    cA
    @0
    @9
    @17
    @34
    @35
    wb
    @10
    @17
    wa
    #
    @34
    @8
    @6
    clt
    wbr
    #
    @6
    @8
    cle
    wbr
    #
    wn
    #
    @35
    @17
    @34
    @6
    cr
    wcel
    #
    @37
    wa
    #
    @10
    @37
    @17
    @8
    cxr
    wcel
    #
    @34
    @41
    wb
    @8
    rexr
    #
    @8
    @6
    elioopnf
    syl
    @10
    @37
    @41
    @10
    @40
    @37
    @13
    biantrurd
    bicomd
    sylan9bbr
    @10
    @40
    @17
    @37
    @39
    wb
    #
    @13
    @17
    @40
    @44
    @8
    @6
    ltnle
    ancoms
    sylan
    @36
    @39
    @5
    @24
    wcel
    #
    wn
    #
    @5
    @20
    wcel
    #
    wn
    #
    wa
    #
    wn
    #
    @35
    @36
    @38
    @49
    @36
    @38
    @23
    @5
    cle
    wbr
    #
    @5
    @8
    cle
    wbr
    #
    wa
    #
    @49
    @10
    @5
    cr
    wcel
    #
    @17
    @38
    @53
    wb
    @11
    @5
    @8
    absle
    sylan
    @36
    @51
    @46
    @52
    @48
    @36
    @51
    @5
    @23
    clt
    wbr
    #
    wn
    #
    @46
    @17
    @23
    cr
    wcel
    @54
    @51
    @56
    wb
    @10
    @8
    renegcl
    #
    @11
    @23
    @5
    lenlt
    syl2anr
    @36
    @55
    @45
    @10
    @55
    @54
    @55
    wa
    #
    @17
    @45
    @10
    @54
    @55
    @11
    biantrurd
    @17
    @45
    @58
    @17
    @23
    cxr
    wcel
    #
    @45
    @58
    wb
    @17
    @23
    @57
    rexrd
    #
    @23
    @5
    elioomnf
    syl
    bicomd
    sylan9bb
    notbid
    bitrd
    @36
    @52
    @8
    @5
    clt
    wbr
    #
    wn
    #
    @48
    @10
    @54
    @17
    @52
    @62
    wb
    @11
    @5
    @8
    lenlt
    sylan
    @36
    @61
    @47
    @10
    @61
    @54
    @61
    wa
    #
    @17
    @47
    @10
    @54
    @61
    @11
    biantrurd
    @17
    @47
    @63
    @17
    @42
    @47
    @63
    wb
    @43
    @8
    @5
    elioopnf
    syl
    bicomd
    sylan9bb
    notbid
    bitrd
    anbi12d
    bitrd
    notbid
    @35
    @45
    @47
    wo
    @50
    @5
    @24
    @20
    elun
    @45
    @47
    oran
    bitri
    syl6bbr
    3bitrd
    an32s
    rabbidva
    vt
    cA
    @6
    @20
    @7
    @14
    mptpreima
    vt
    cA
    @5
    @29
    @31
    @31
    eqid
    #
    mptpreima
    3eqtr4g
    @28
    @22
    @32
    @29
    @28
    cF
    @31
    @28
    vt
    cA
    cr
    cF
    @0
    @17
    simpl
    feqmptd
    cnveqd
    #
    imaeq1d
    eqtr4d
    @22
    @24
    @20
    imaundi
    syl6eq
    adantlr
    @2
    @27
    @16
    wcel
    #
    @17
    @1
    @0
    @66
    @1
    @0
    wa
    @25
    @16
    wcel
    @26
    @16
    wcel
    @66
    cA
    cmnf
    @23
    cF
    mbfima
    cA
    @8
    cpnf
    cF
    mbfima
    @25
    @26
    unmbl
    syl2anc
    ancoms
    adantr
    eqeltrd
    @18
    @19
    cmnf
    @8
    cioo
    co
    #
    cima
    #
    @22
    @23
    @8
    cioo
    co
    #
    cima
    #
    @16
    @0
    @17
    @68
    @70
    wceq
    @1
    @28
    @68
    @32
    @69
    cima
    #
    @70
    @28
    @6
    @67
    wcel
    #
    vt
    cA
    crab
    @5
    @69
    wcel
    #
    vt
    cA
    crab
    @68
    @71
    @28
    @72
    @73
    vt
    cA
    @0
    @9
    @17
    @72
    @73
    wb
    @36
    @6
    @8
    clt
    wbr
    #
    @23
    @5
    clt
    wbr
    @5
    @8
    clt
    wbr
    wa
    #
    @72
    @73
    @10
    @54
    @17
    @74
    @75
    wb
    @11
    @5
    @8
    abslt
    sylan
    @17
    @72
    @40
    @74
    wa
    #
    @10
    @74
    @17
    @42
    @72
    @76
    wb
    @43
    @8
    @6
    elioomnf
    syl
    @10
    @74
    @76
    @10
    @40
    @74
    @13
    biantrurd
    bicomd
    sylan9bbr
    @17
    @59
    @42
    wa
    @5
    cxr
    wcel
    #
    @73
    @75
    wb
    #
    @10
    @17
    @59
    @42
    @60
    @43
    jca
    @10
    @5
    @11
    rexrd
    @59
    @42
    @77
    @78
    @23
    @8
    @5
    elioo5
    3expa
    syl2anr
    3bitr4d
    an32s
    rabbidva
    vt
    cA
    @6
    @67
    @7
    @14
    mptpreima
    vt
    cA
    @5
    @69
    @31
    @64
    mptpreima
    3eqtr4g
    @28
    @22
    @32
    @69
    @65
    imaeq1d
    eqtr4d
    adantlr
    @2
    @70
    @16
    wcel
    #
    @17
    @1
    @0
    @79
    cA
    @23
    @8
    cF
    mbfima
    ancoms
    adantr
    eqeltrd
    ismbf2d
    eqeltrd
end
