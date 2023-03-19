include "caddc.mm"
include "cmul.mm"
include "cop.mm"
include "cabs.mm"
include "ccphlo.mm"
include "wcel.mm"
include "cnv.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "c1.mm"
include "cneg.mm"
include "wceq.mm"
include "cc.mm"
include "wral.mm"
include "eqid.mm"
include "cnnv.mm"
include "wa.mm"
include "cmin.mm"
include "mulm1.mm"
include "adantl.mm"
include "oveq2d.mm"
include "negsub.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "ccj.mm"
include "cre.mm"
include "sqabsadd.mm"
include "sqabssub.mm"
include "oveq12d.mm"
include "abscl.mm"
include "recnd.mm"
include "sqcld.mm"
include "addcl.mm"
include "syl2an.mm"
include "2cn.mm"
include "cjcl.mm"
include "mulcl.mm"
include "sylan2.mm"
include "recl.mm"
include "syl.mm"
include "sylancr.mm"
include "ppncand.mm"
include "2times.mm"
include "eqcomd.mm"
include "rgen2a.mm"
include "cvv.mm"
include "wb.mm"
include "addex.mm"
include "mulex.mm"
include "cr.mm"
include "wf.mm"
include "absf.mm"
include "cnex.mm"
include "fex.mm"
include "mp2an.mm"
include "cablo.mm"
include "cgr.mm"
include "cnaddabloOLD.mm"
include "ablogrpo.mm"
include "ax-mp.mm"
include "cxp.mm"
include "ax-addf.mm"
include "fdmi.mm"
include "grporn.mm"
include "isphg.mm"
include "mp3an.mm"
include "mpbir2an.mm"
include "eqeltri.mm"

theorem cncph
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  assume cncph.6: |- U = <. <. + , x. >. , abs >.


  assert |- U e. CPreHilOLD

  proof
    cU
    caddc
    cmul
    cop
    cabs
    cop
    #
    ccphlo
    cncph.6
    @0
    ccphlo
    wcel
    #
    @0
    cnv
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    caddc
    co
    cabs
    cfv
    c2
    cexp
    co
    #
    @3
    c1
    cneg
    @4
    cmul
    co
    #
    caddc
    co
    #
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    c2
    @3
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    @4
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    cmul
    co
    #
    wceq
    #
    vy
    cc
    wral
    vx
    cc
    wral
    #
    @0
    @0
    eqid
    cnnv
    @17
    vx
    vy
    cc
    @3
    cc
    wcel
    #
    @4
    cc
    wcel
    #
    wa
    #
    @10
    @5
    @3
    @4
    cmin
    co
    #
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    @16
    @21
    @9
    @24
    @5
    caddc
    @21
    @8
    @23
    c2
    cexp
    @21
    @7
    @22
    cabs
    @21
    @7
    @3
    @4
    cneg
    #
    caddc
    co
    @22
    @21
    @6
    @26
    @3
    caddc
    @20
    @6
    @26
    wceq
    @19
    @4
    mulm1
    adantl
    oveq2d
    @3
    @4
    negsub
    eqtrd
    fveq2d
    oveq1d
    oveq2d
    @21
    @25
    @15
    @15
    caddc
    co
    #
    @16
    @21
    @25
    @15
    c2
    @3
    @4
    ccj
    cfv
    #
    cmul
    co
    #
    cre
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    @15
    @31
    cmin
    co
    #
    caddc
    co
    @27
    @21
    @5
    @32
    @24
    @33
    caddc
    @3
    @4
    sqabsadd
    @3
    @4
    sqabssub
    oveq12d
    @21
    @15
    @31
    @15
    @19
    @12
    cc
    wcel
    @14
    cc
    wcel
    @15
    cc
    wcel
    #
    @20
    @19
    @11
    @19
    @11
    @3
    abscl
    recnd
    sqcld
    @20
    @13
    @20
    @13
    @4
    abscl
    recnd
    sqcld
    @12
    @14
    addcl
    syl2an
    #
    @21
    c2
    cc
    wcel
    @30
    cc
    wcel
    #
    @31
    cc
    wcel
    2cn
    @21
    @29
    cc
    wcel
    #
    @36
    @20
    @19
    @28
    cc
    wcel
    @37
    @4
    cjcl
    @3
    @28
    mulcl
    sylan2
    @37
    @30
    @29
    recl
    recnd
    syl
    c2
    @30
    mulcl
    sylancr
    @35
    ppncand
    eqtrd
    @21
    @34
    @27
    @16
    wceq
    @35
    @34
    @16
    @27
    @15
    2times
    eqcomd
    syl
    eqtrd
    eqtrd
    rgen2a
    caddc
    cvv
    wcel
    cmul
    cvv
    wcel
    cabs
    cvv
    wcel
    #
    @1
    @2
    @18
    wa
    wb
    addex
    mulex
    cc
    cr
    cabs
    wf
    cc
    cvv
    wcel
    @38
    absf
    cnex
    cc
    cr
    cvv
    cabs
    fex
    mp2an
    vx
    vy
    cvv
    cvv
    cvv
    cmul
    caddc
    cabs
    cc
    caddc
    cc
    caddc
    cablo
    wcel
    caddc
    cgr
    wcel
    cnaddabloOLD
    caddc
    ablogrpo
    ax-mp
    cc
    cc
    cxp
    cc
    caddc
    ax-addf
    fdmi
    grporn
    isphg
    mp3an
    mpbir2an
    eqeltri
end
