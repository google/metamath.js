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
include "weq.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "cbvral.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "nfcv.mm"
include "cbvmpt.mm"
include "syl5eqelr.mm"
include "iblmulc2nc.mm"
include "adantr.mm"
include "mulcld.mm"
include "iblcn.mm"
include "mpbid.mm"
include "simpld.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "absmuld.mm"
include "mpteq2dva.mm"
include "cvol.mm"
include "cdm.mm"
include "cr.mm"
include "mbfdm2.mm"
include "abscld.mm"
include "fconstmpt.mm"
include "a1i.mm"
include "nffv.mm"
include "fveq2d.mm"
include "offval2.mm"
include "eqtr4d.mm"
include "recnd.mm"
include "eqid.mm"
include "fmptd.mm"
include "mbfmulc2re.mm"
include "eqeltrd.mm"
include "iblabsnc.mm"
include "recld.mm"
include "releabsd.mm"
include "itgle.mm"
include "c2.mm"
include "cexp.mm"
include "sqvald.mm"
include "absvalsqd.mm"
include "mulcomd.mm"
include "cbvitg.mm"
include "oveq2i.mm"
include "itgmulc2nc.mm"
include "syl5eq.mm"
include "3eqtrd.mm"
include "resqcld.mm"
include "rered.mm"
include "cvv.mm"
include "ovexd.mm"
include "itgre.mm"
include "3eqtr3d.mm"
include "eqtr3d.mm"
include "eqeltrrd.mm"
include "abscjd.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "itgeq2dv.mm"
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

theorem itgabsnc
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  assume itgabsnc.1: |- ( ( ph /\ x e. A ) -> B e. V )
  assume itgabsnc.2: |- ( ph -> ( x e. A |-> B ) e. L^1 )
  assume itgabsnc.m1: |- ( ph -> ( x e. A |-> ( abs ` B ) ) e. MblFn )
  assume itgabsnc.m2: |- ( ph -> ( y e. A |-> ( ( * ` S. A B _d x ) x. [_ y / x ]_ B ) ) e. MblFn )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint ph x
  disjoint ph y
  disjoint V x
  disjoint V y
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
    itgabsnc.1
    itgabsnc.2
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
    itgabsnc.2
    @25
    iblmbf
    syl
    #
    itgabsnc.1
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
    vy
    weq
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
    @28
    @30
    cbvmpt
    itgabsnc.2
    syl5eqelr
    #
    itgabsnc.m2
    iblmulc2nc
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
    cc
    @38
    @34
    wph
    vy
    cA
    @17
    cmpt
    #
    cA
    @11
    cabs
    cfv
    #
    csn
    cxp
    #
    vx
    cA
    @3
    cmpt
    #
    cmul
    cof
    #
    co
    #
    cmbf
    wph
    @39
    vy
    cA
    @40
    @13
    cabs
    cfv
    #
    cmul
    co
    #
    cmpt
    @44
    wph
    vy
    cA
    @17
    @46
    @36
    @11
    @13
    @37
    @31
    absmuld
    #
    mpteq2dva
    wph
    vy
    cA
    @40
    @45
    cmul
    @41
    @42
    cvol
    cdm
    #
    cr
    cr
    wph
    vx
    cA
    cB
    cV
    @26
    itgabsnc.1
    mbfdm2
    #
    @36
    @11
    @37
    abscld
    @36
    @13
    @31
    abscld
    #
    @41
    vy
    cA
    @40
    cmpt
    wceq
    wph
    vy
    cA
    @40
    fconstmpt
    a1i
    @42
    vy
    cA
    @45
    cmpt
    #
    wceq
    wph
    vx
    vy
    cA
    @3
    @45
    vy
    @3
    nfcv
    #
    vx
    @13
    cabs
    vx
    cabs
    nfcv
    @28
    nffv
    #
    @29
    cB
    @13
    cabs
    @30
    fveq2d
    #
    cbvmpt
    #
    a1i
    #
    offval2
    eqtr4d
    wph
    cA
    @40
    @42
    itgabsnc.m1
    wph
    @11
    @22
    abscld
    wph
    vx
    cA
    @3
    cc
    @42
    wph
    vx
    cv
    cA
    wcel
    wa
    #
    @3
    @57
    cB
    @27
    abscld
    #
    recnd
    @42
    eqid
    fmptd
    #
    mbfmulc2re
    eqeltrd
    iblabsnc
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
    @60
    cre
    cfv
    vy
    cA
    @14
    citg
    #
    cre
    cfv
    @60
    @16
    wph
    @60
    @63
    cre
    wph
    @60
    @0
    @11
    cmul
    co
    @11
    @0
    cmul
    co
    #
    @63
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
    @64
    @11
    vy
    cA
    @13
    citg
    #
    cmul
    co
    @63
    @0
    @65
    @11
    cmul
    vx
    vy
    cA
    cB
    @13
    @30
    @32
    @28
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
    itgabsnc.m2
    itgmulc2nc
    syl5eq
    3eqtrd
    fveq2d
    wph
    @60
    wph
    @1
    @61
    resqcld
    rered
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
    @34
    itgre
    3eqtr3d
    eqtr3d
    wph
    @9
    @1
    vy
    cA
    @45
    citg
    #
    cmul
    co
    #
    @18
    @4
    @66
    @1
    cmul
    vx
    vy
    cA
    @3
    @45
    @54
    @52
    @53
    cbvitg
    oveq2i
    wph
    @67
    vy
    cA
    @1
    @45
    cmul
    co
    #
    citg
    @18
    wph
    vy
    cA
    @45
    @1
    cr
    @62
    @50
    wph
    @51
    @42
    cibl
    @55
    wph
    vx
    cA
    cB
    cV
    itgabsnc.1
    itgabsnc.2
    itgabsnc.m1
    iblabsnc
    #
    syl5eqelr
    wph
    cA
    @1
    csn
    cxp
    #
    @42
    @43
    co
    vy
    cA
    @68
    cmpt
    cmbf
    wph
    vy
    cA
    @1
    @45
    cmul
    @70
    @42
    @48
    cr
    cr
    @49
    wph
    @1
    cr
    wcel
    #
    @35
    @61
    adantr
    @50
    @70
    vy
    cA
    @1
    cmpt
    wceq
    wph
    vy
    cA
    @1
    fconstmpt
    a1i
    @56
    offval2
    wph
    cA
    @1
    @42
    itgabsnc.m1
    @61
    @59
    mbfmulc2re
    eqeltrrd
    itgmulc2nc
    wph
    vy
    cA
    @17
    @68
    @36
    @17
    @46
    @68
    @47
    @36
    @40
    @1
    @45
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
    @71
    @4
    cr
    wcel
    #
    @71
    @2
    @5
    @10
    wb
    wph
    @71
    @2
    @61
    adantr
    #
    wph
    @72
    @2
    wph
    vx
    cA
    @3
    @58
    @69
    itgrecl
    adantr
    @73
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
    @69
    @58
    @57
    cB
    @27
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
    @71
    @74
    @75
    wb
    0re
    @61
    cc0
    @1
    leloe
    sylancr
    mpbid
    mpjaod
end
