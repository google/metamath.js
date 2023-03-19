include "cbs.mm"
include "cfv.mm"
include "cmap.mm"
include "co.mm"
include "chom.mm"
include "crn.mm"
include "cuni.mm"
include "cxp.mm"
include "cpw.mm"
include "cfunc.mm"
include "c1.mm"
include "df-base.mm"
include "wunstr.mm"
include "wunmap.mm"
include "c4.mm"
include "cdc.mm"
include "df-hom.mm"
include "wunrn.mm"
include "wununi.mm"
include "wunxp.mm"
include "wunpw.mm"
include "wrel.mm"
include "relfunc.mm"
include "a1i.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wbr.mm"
include "df-br.mm"
include "wa.mm"
include "wf.mm"
include "eqid.mm"
include "simpr.mm"
include "funcf1.mm"
include "fvex.mm"
include "elmap.mm"
include "sylibr.mm"
include "c1st.mm"
include "c2nd.mm"
include "cixp.mm"
include "wss.mm"
include "wral.mm"
include "mapsspw.mm"
include "fvssunirn.mm"
include "ovssunirn.mm"
include "xpss12.mm"
include "mp2an.mm"
include "sspwb.mm"
include "mpbi.mm"
include "sstri.mm"
include "rgenw.mm"
include "ss2ixp.mm"
include "ax-mp.mm"
include "xpex.mm"
include "rnex.mm"
include "uniex.mm"
include "pwex.mm"
include "ixpconst.mm"
include "sseqtri.mm"
include "funcixp.mm"
include "sseldi.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "ex.mm"
include "syl5bir.mm"
include "relssdv.mm"
include "wunss.mm"

theorem wunfunc
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let vz: setvar z
  assume wunfunc.1: |- ( ph -> U e. WUni )
  assume wunfunc.2: |- ( ph -> C e. U )
  assume wunfunc.3: |- ( ph -> D e. U )


  assert |- ( ph -> ( C Func D ) e. U )

  proof
    wph
    cD
    cbs
    cfv
    #
    cC
    cbs
    cfv
    #
    cmap
    co
    #
    cC
    chom
    cfv
    #
    crn
    #
    cuni
    #
    cD
    chom
    cfv
    #
    crn
    #
    cuni
    #
    cxp
    #
    cpw
    #
    @1
    @1
    cxp
    #
    cmap
    co
    #
    cxp
    #
    cC
    cD
    cfunc
    co
    #
    cU
    wunfunc.1
    wph
    @2
    @12
    cU
    wunfunc.1
    wph
    @0
    @1
    cU
    wunfunc.1
    wph
    cD
    cU
    cbs
    c1
    df-base
    wunfunc.1
    wunfunc.3
    wunstr
    wph
    cC
    cU
    cbs
    c1
    df-base
    wunfunc.1
    wunfunc.2
    wunstr
    #
    wunmap
    wph
    @10
    @11
    cU
    wunfunc.1
    wph
    @9
    cU
    wunfunc.1
    wph
    @5
    @8
    cU
    wunfunc.1
    wph
    @4
    cU
    wunfunc.1
    wph
    @3
    cU
    wunfunc.1
    wph
    cC
    cU
    chom
    c1
    c4
    cdc
    #
    df-hom
    wunfunc.1
    wunfunc.2
    wunstr
    wunrn
    wununi
    wph
    @7
    cU
    wunfunc.1
    wph
    @6
    cU
    wunfunc.1
    wph
    cD
    cU
    chom
    @16
    df-hom
    wunfunc.1
    wunfunc.3
    wunstr
    wunrn
    wununi
    wunxp
    wunpw
    wph
    @1
    @1
    cU
    wunfunc.1
    @15
    @15
    wunxp
    wunmap
    wunxp
    wph
    vf
    vg
    @14
    @13
    @14
    wrel
    wph
    cC
    cD
    relfunc
    a1i
    vf
    cv
    #
    vg
    cv
    #
    cop
    #
    @14
    wcel
    @17
    @18
    @14
    wbr
    #
    wph
    @19
    @13
    wcel
    #
    @17
    @18
    @14
    df-br
    wph
    @20
    @21
    wph
    @20
    wa
    #
    @17
    @2
    wcel
    #
    @18
    @12
    wcel
    @21
    @22
    @1
    @0
    @17
    wf
    @23
    @22
    @1
    @0
    cC
    cD
    @17
    @18
    @1
    eqid
    #
    @0
    eqid
    wph
    @20
    simpr
    #
    funcf1
    @0
    @1
    @17
    cD
    cbs
    fvex
    cC
    cbs
    fvex
    #
    elmap
    sylibr
    @22
    vz
    @11
    vz
    cv
    #
    c1st
    cfv
    @17
    cfv
    #
    @27
    c2nd
    cfv
    @17
    cfv
    #
    @6
    co
    #
    @27
    @3
    cfv
    #
    cmap
    co
    #
    cixp
    #
    @12
    @18
    @33
    vz
    @11
    @10
    cixp
    #
    @12
    @32
    @10
    wss
    #
    vz
    @11
    wral
    @33
    @34
    wss
    @35
    vz
    @11
    @32
    @31
    @30
    cxp
    #
    cpw
    #
    @10
    @30
    @31
    mapsspw
    @36
    @9
    wss
    #
    @37
    @10
    wss
    @31
    @5
    wss
    @30
    @8
    wss
    @38
    @3
    @27
    fvssunirn
    @6
    @28
    @29
    ovssunirn
    @31
    @5
    @30
    @8
    xpss12
    mp2an
    @36
    @9
    sspwb
    mpbi
    sstri
    rgenw
    vz
    @11
    @32
    @10
    ss2ixp
    ax-mp
    vz
    @11
    @10
    @1
    @1
    @26
    @26
    xpex
    @9
    @5
    @8
    @4
    @3
    cC
    chom
    fvex
    rnex
    uniex
    @7
    @6
    cD
    chom
    fvex
    rnex
    uniex
    xpex
    pwex
    ixpconst
    sseqtri
    @22
    vz
    @1
    cC
    cD
    @17
    @18
    @3
    @6
    @24
    @3
    eqid
    @6
    eqid
    @25
    funcixp
    sseldi
    @17
    @18
    @2
    @12
    opelxpi
    syl2anc
    ex
    syl5bir
    relssdv
    wunss
end
