include "cmbf.mm"
include "wcel.mm"
include "cvol.mm"
include "cdm.mm"
include "wa.mm"
include "cres.mm"
include "cre.mm"
include "ccom.mm"
include "cim.mm"
include "cc.mm"
include "cr.mm"
include "wf.mm"
include "ref.mm"
include "wss.mm"
include "cpm.mm"
include "co.mm"
include "simpr.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cioo.mm"
include "crn.mm"
include "wral.mm"
include "ismbf1.mm"
include "simplbi.mm"
include "adantr.mm"
include "pmresg.mm"
include "syl2anc.mm"
include "cvv.mm"
include "wb.mm"
include "cnex.mm"
include "elpm2g.mm"
include "sylancr.mm"
include "mpbid.mm"
include "simpld.mm"
include "fco.mm"
include "cin.mm"
include "dmres.mm"
include "id.mm"
include "mbfdm.mm"
include "inmbl.mm"
include "syl2anr.mm"
include "syl5eqel.mm"
include "cpnf.mm"
include "resco.mm"
include "cnveqi.mm"
include "imaeq1i.mm"
include "cnvresima.mm"
include "eqtr3i.mm"
include "mbff.mm"
include "ismbfcn.mm"
include "syl.mm"
include "ibi.mm"
include "mbfima.mm"
include "sylan.mm"
include "cmnf.mm"
include "ismbf2d.mm"
include "imf.mm"
include "simprd.mm"
include "mpbir2and.mm"

theorem mbfres
  let cA: class A
  let cF: class F
  let vx: setvar x


  assert |- ( ( F e. MblFn /\ A e. dom vol ) -> ( F |` A ) e. MblFn )

  proof
    cF
    cmbf
    wcel
    #
    cA
    cvol
    cdm
    #
    wcel
    #
    wa
    #
    cF
    cA
    cres
    #
    cmbf
    wcel
    #
    cre
    @4
    ccom
    #
    cmbf
    wcel
    #
    cim
    @4
    ccom
    #
    cmbf
    wcel
    #
    @3
    vx
    @4
    cdm
    #
    @6
    @3
    cc
    cr
    cre
    wf
    #
    @10
    cc
    @4
    wf
    #
    @10
    cr
    @6
    wf
    ref
    @3
    @12
    @10
    cA
    wss
    #
    @3
    @4
    cc
    cA
    cpm
    co
    wcel
    #
    @12
    @13
    wa
    #
    @3
    @2
    cF
    cc
    cr
    cpm
    co
    wcel
    #
    @14
    @0
    @2
    simpr
    #
    @0
    @16
    @2
    @0
    @16
    cre
    cF
    ccom
    #
    ccnv
    #
    vx
    cv
    #
    cima
    @1
    wcel
    cim
    cF
    ccom
    #
    ccnv
    #
    @20
    cima
    @1
    wcel
    wa
    vx
    cioo
    crn
    wral
    vx
    cF
    ismbf1
    simplbi
    adantr
    cc
    cA
    cr
    cF
    @1
    pmresg
    syl2anc
    @3
    cc
    cvv
    wcel
    @2
    @14
    @15
    wb
    cnex
    @17
    cc
    cA
    @4
    cvv
    @1
    elpm2g
    sylancr
    mpbid
    simpld
    #
    @10
    cc
    cr
    cre
    @4
    fco
    sylancr
    @3
    @10
    cA
    cF
    cdm
    #
    cin
    #
    @1
    cF
    cA
    dmres
    @2
    @2
    @24
    @1
    wcel
    @25
    @1
    wcel
    @0
    @2
    id
    cF
    mbfdm
    cA
    @24
    inmbl
    syl2anr
    syl5eqel
    #
    @3
    @6
    ccnv
    #
    @20
    cpnf
    cioo
    co
    #
    cima
    #
    @1
    wcel
    @20
    cr
    wcel
    #
    @3
    @29
    @19
    @28
    cima
    #
    cA
    cin
    #
    @1
    @18
    cA
    cres
    #
    ccnv
    #
    @28
    cima
    @29
    @32
    @34
    @27
    @28
    @33
    @6
    cre
    cF
    cA
    resco
    cnveqi
    #
    imaeq1i
    cA
    @28
    @18
    cnvresima
    eqtr3i
    @0
    @31
    @1
    wcel
    #
    @2
    @32
    @1
    wcel
    @0
    @18
    cmbf
    wcel
    #
    @24
    cr
    @18
    wf
    #
    @36
    @0
    @37
    @21
    cmbf
    wcel
    #
    @0
    @37
    @39
    wa
    #
    @0
    @24
    cc
    cF
    wf
    #
    @0
    @40
    wb
    cF
    mbff
    #
    @24
    cF
    ismbfcn
    syl
    ibi
    #
    simpld
    #
    @0
    @11
    @41
    @38
    ref
    @42
    @24
    cc
    cr
    cre
    cF
    fco
    sylancr
    #
    @24
    @20
    cpnf
    @18
    mbfima
    syl2anc
    @31
    cA
    inmbl
    sylan
    syl5eqel
    adantr
    @3
    @27
    cmnf
    @20
    cioo
    co
    #
    cima
    #
    @1
    wcel
    @30
    @3
    @47
    @19
    @46
    cima
    #
    cA
    cin
    #
    @1
    @34
    @46
    cima
    @47
    @49
    @34
    @27
    @46
    @35
    imaeq1i
    cA
    @46
    @18
    cnvresima
    eqtr3i
    @0
    @48
    @1
    wcel
    #
    @2
    @49
    @1
    wcel
    @0
    @37
    @38
    @50
    @44
    @45
    @24
    cmnf
    @20
    @18
    mbfima
    syl2anc
    @48
    cA
    inmbl
    sylan
    syl5eqel
    adantr
    ismbf2d
    @3
    vx
    @10
    @8
    @3
    cc
    cr
    cim
    wf
    #
    @12
    @10
    cr
    @8
    wf
    imf
    @23
    @10
    cc
    cr
    cim
    @4
    fco
    sylancr
    @26
    @3
    @8
    ccnv
    #
    @28
    cima
    #
    @1
    wcel
    @30
    @3
    @53
    @22
    @28
    cima
    #
    cA
    cin
    #
    @1
    @21
    cA
    cres
    #
    ccnv
    #
    @28
    cima
    @53
    @55
    @57
    @52
    @28
    @56
    @8
    cim
    cF
    cA
    resco
    cnveqi
    #
    imaeq1i
    cA
    @28
    @21
    cnvresima
    eqtr3i
    @0
    @54
    @1
    wcel
    #
    @2
    @55
    @1
    wcel
    @0
    @39
    @24
    cr
    @21
    wf
    #
    @59
    @0
    @37
    @39
    @43
    simprd
    #
    @0
    @51
    @41
    @60
    imf
    @42
    @24
    cc
    cr
    cim
    cF
    fco
    sylancr
    #
    @24
    @20
    cpnf
    @21
    mbfima
    syl2anc
    @54
    cA
    inmbl
    sylan
    syl5eqel
    adantr
    @3
    @52
    @46
    cima
    #
    @1
    wcel
    @30
    @3
    @63
    @22
    @46
    cima
    #
    cA
    cin
    #
    @1
    @57
    @46
    cima
    @63
    @65
    @57
    @52
    @46
    @58
    imaeq1i
    cA
    @46
    @21
    cnvresima
    eqtr3i
    @0
    @64
    @1
    wcel
    #
    @2
    @65
    @1
    wcel
    @0
    @39
    @60
    @66
    @61
    @62
    @24
    cmnf
    @20
    @21
    mbfima
    syl2anc
    @64
    cA
    inmbl
    sylan
    syl5eqel
    adantr
    ismbf2d
    @3
    @12
    @5
    @7
    @9
    wa
    wb
    @23
    @10
    @4
    ismbfcn
    syl
    mpbir2and
end
