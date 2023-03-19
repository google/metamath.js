include "cc0.mm"
include "citg.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wceq.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "ccj.mm"
include "cv.mm"
include "csb.mm"
include "cre.mm"
include "cmpt.mm"
include "cibl.mm"
include "wcel.mm"
include "cim.mm"
include "cc.mm"
include "itgcl.mm"
include "cjcld.mm"
include "wral.mm"
include "cmbf.mm"
include "iblmbf.mm"
include "syl.mm"
include "mbfmptcl.mm"
include "ralrimiva.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "cbvral.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "nfcv.mm"
include "cbvmpt.mm"
include "syl5eqelr.mm"
include "iblmulc2.mm"
include "adantr.mm"
include "mulcld.mm"
include "iblcn.mm"
include "mpbid.mm"
include "simpld.mm"
include "cvv.mm"
include "ovexd.mm"
include "iblabs.mm"
include "recld.mm"
include "abscld.mm"
include "releabsd.mm"
include "itgle.mm"
include "c2.mm"
include "cexp.mm"
include "recnd.mm"
include "sqvald.mm"
include "absvalsqd.mm"
include "mulcomd.mm"
include "cbvitg.mm"
include "oveq2i.mm"
include "itgmulc2.mm"
include "syl5eq.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "resqcld.mm"
include "rered.mm"
include "itgre.mm"
include "3eqtr3d.mm"
include "eqtr3d.mm"
include "nffv.mm"
include "cr.mm"
include "absmuld.mm"
include "abscjd.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "itgeq2dv.mm"
include "eqtr4d.mm"
include "3brtr4d.mm"
include "wb.mm"
include "itgrecl.mm"
include "simpr.mm"
include "lemul2.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "ex.mm"
include "absge0d.mm"
include "itgge0.mm"
include "breq1.mm"
include "syl5ibcom.mm"
include "wo.mm"
include "0re.mm"
include "leloe.mm"
include "sylancr.mm"
include "mpjaod.mm"

theorem itgabs
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vy: setvar y
  assume itgabs.1: |- ( ( ph /\ x e. A ) -> B e. V )
  assume itgabs.2: |- ( ph -> ( x e. A |-> B ) e. L^1 )

  disjoint A x
  disjoint ph x
  disjoint V x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint ph y
  assert |- ( ph -> ( abs ` S. A B _d x ) <_ S. A ( abs ` B ) _d x )

  proof
    wph
    cc0
    vx
    cA
    cB
    citg
    #
    cabs
    cfv
    #
    clt
    wbr
    #
    @1
    vx
    cA
    cB
    cabs
    cfv
    #
    citg
    #
    cle
    wbr
    #
    cc0
    @1
    wceq
    #
    wph
    @2
    @5
    wph
    @2
    wa
    #
    @5
    @1
    @1
    cmul
    co
    #
    @1
    @4
    cmul
    co
    #
    cle
    wbr
    #
    wph
    @10
    @2
    wph
    vy
    cA
    @0
    ccj
    cfv
    #
    vx
    vy
    cv
    #
    cB
    csb
    #
    cmul
    co
    #
    cre
    cfv
    #
    citg
    #
    vy
    cA
    @14
    cabs
    cfv
    #
    citg
    #
    @8
    @9
    cle
    wph
    vy
    cA
    @15
    @17
    wph
    vy
    cA
    @15
    cmpt
    cibl
    wcel
    #
    vy
    cA
    @14
    cim
    cfv
    cmpt
    cibl
    wcel
    #
    wph
    vy
    cA
    @14
    cmpt
    cibl
    wcel
    @19
    @20
    wa
    wph
    vy
    cA
    @13
    @11
    cc
    wph
    @0
    wph
    vx
    cA
    cB
    cV
    itgabs.1
    itgabs.2
    itgcl
    #
    cjcld
    #
    wph
    @13
    cc
    wcel
    #
    vy
    cA
    wph
    cB
    cc
    wcel
    #
    vx
    cA
    wral
    @23
    vy
    cA
    wral
    wph
    @24
    vx
    cA
    wph
    vx
    cA
    cB
    cV
    wph
    vx
    cA
    cB
    cmpt
    #
    cibl
    wcel
    @25
    cmbf
    wcel
    itgabs.2
    @25
    iblmbf
    syl
    itgabs.1
    mbfmptcl
    #
    ralrimiva
    @24
    @23
    vx
    vy
    cA
    @24
    vy
    nfv
    vx
    @13
    cc
    vx
    @12
    cB
    nfcsb1v
    #
    nfel1
    vx
    cv
    #
    @12
    wceq
    #
    cB
    @13
    cc
    vx
    @12
    cB
    csbeq1a
    #
    eleq1d
    cbvral
    sylib
    r19.21bi
    #
    wph
    vy
    cA
    @13
    cmpt
    @25
    cibl
    vx
    vy
    cA
    cB
    @13
    vy
    cB
    nfcv
    #
    @27
    @30
    cbvmpt
    itgabs.2
    syl5eqelr
    #
    iblmulc2
    #
    wph
    vy
    cA
    @14
    wph
    @12
    cA
    wcel
    #
    wa
    #
    @11
    @13
    wph
    @11
    cc
    wcel
    @35
    @22
    adantr
    #
    @31
    mulcld
    #
    iblcn
    mpbid
    simpld
    wph
    vy
    cA
    @14
    cvv
    @36
    @11
    @13
    cmul
    ovexd
    #
    @34
    iblabs
    @36
    @14
    @38
    recld
    @36
    @14
    @38
    abscld
    @36
    @14
    @38
    releabsd
    itgle
    wph
    @1
    c2
    cexp
    co
    #
    @8
    @16
    wph
    @1
    wph
    @1
    wph
    @0
    @21
    abscld
    #
    recnd
    #
    sqvald
    wph
    @40
    cre
    cfv
    vy
    cA
    @14
    citg
    #
    cre
    cfv
    @40
    @16
    wph
    @40
    @43
    cre
    wph
    @40
    @0
    @11
    cmul
    co
    @11
    @0
    cmul
    co
    #
    @43
    wph
    @0
    @21
    absvalsqd
    wph
    @0
    @11
    @21
    @22
    mulcomd
    wph
    @44
    @11
    vy
    cA
    @13
    citg
    #
    cmul
    co
    @43
    @0
    @45
    @11
    cmul
    vx
    vy
    cA
    cB
    @13
    @30
    @32
    @27
    cbvitg
    oveq2i
    wph
    vy
    cA
    @13
    @11
    cc
    @22
    @31
    @33
    itgmulc2
    syl5eq
    3eqtrd
    fveq2d
    wph
    @40
    wph
    @1
    @41
    resqcld
    rered
    wph
    vy
    cA
    @14
    cvv
    @39
    @34
    itgre
    3eqtr3d
    eqtr3d
    wph
    @9
    @1
    vy
    cA
    @13
    cabs
    cfv
    #
    citg
    #
    cmul
    co
    #
    @18
    @4
    @47
    @1
    cmul
    vx
    vy
    cA
    @3
    @46
    @29
    cB
    @13
    cabs
    @30
    fveq2d
    vy
    @3
    nfcv
    vx
    @13
    cabs
    vx
    cabs
    nfcv
    @27
    nffv
    cbvitg
    oveq2i
    wph
    @48
    vy
    cA
    @1
    @46
    cmul
    co
    #
    citg
    @18
    wph
    vy
    cA
    @46
    @1
    cr
    @42
    @36
    @13
    @31
    abscld
    wph
    vy
    cA
    @13
    cc
    @31
    @33
    iblabs
    itgmulc2
    wph
    vy
    cA
    @17
    @49
    @36
    @17
    @11
    cabs
    cfv
    #
    @46
    cmul
    co
    @49
    @36
    @11
    @13
    @37
    @31
    absmuld
    @36
    @50
    @1
    @46
    cmul
    @36
    @0
    wph
    @0
    cc
    wcel
    @35
    @21
    adantr
    abscjd
    oveq1d
    eqtrd
    itgeq2dv
    eqtr4d
    syl5eq
    3brtr4d
    adantr
    @7
    @1
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    @51
    @2
    @5
    @10
    wb
    wph
    @51
    @2
    @41
    adantr
    #
    wph
    @52
    @2
    wph
    vx
    cA
    @3
    wph
    @28
    cA
    wcel
    wa
    #
    cB
    @26
    abscld
    #
    wph
    vx
    cA
    cB
    cV
    itgabs.1
    itgabs.2
    iblabs
    #
    itgrecl
    adantr
    @53
    wph
    @2
    simpr
    @1
    @4
    @1
    lemul2
    syl112anc
    mpbird
    ex
    wph
    cc0
    @4
    cle
    wbr
    @6
    @5
    wph
    vx
    cA
    @3
    @56
    @55
    @54
    cB
    @26
    absge0d
    itgge0
    cc0
    @1
    @4
    cle
    breq1
    syl5ibcom
    wph
    cc0
    @1
    cle
    wbr
    #
    @2
    @6
    wo
    #
    wph
    @0
    @21
    absge0d
    wph
    cc0
    cr
    wcel
    @51
    @57
    @58
    wb
    0re
    @41
    cc0
    @1
    leloe
    sylancr
    mpbid
    mpjaod
end
