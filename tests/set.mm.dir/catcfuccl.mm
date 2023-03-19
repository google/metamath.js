include "ccat.mm"
include "cin.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cfunc.mm"
include "co.mm"
include "cop.mm"
include "chom.mm"
include "cnat.mm"
include "cco.mm"
include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "c2nd.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "csb.mm"
include "ctp.mm"
include "eqid.mm"
include "inss2.mm"
include "cwun.mm"
include "catcbas.mm"
include "eleqtrd.mm"
include "sseldi.mm"
include "eqidd.mm"
include "fucval.mm"
include "c1.mm"
include "df-base.mm"
include "wunndx.mm"
include "wunstr.mm"
include "inss1.mm"
include "wunfunc.mm"
include "wunop.mm"
include "c4.mm"
include "cdc.mm"
include "df-hom.mm"
include "wunnat.mm"
include "c5.mm"
include "df-cco.mm"
include "crn.mm"
include "cuni.mm"
include "cpw.mm"
include "cmap.mm"
include "cpm.mm"
include "wunxp.mm"
include "wunrn.mm"
include "wununi.mm"
include "wunpw.mm"
include "wunmap.mm"
include "wunpm.mm"
include "wf.mm"
include "wcel.mm"
include "wral.mm"
include "cvv.mm"
include "fvex.mm"
include "wsbc.mm"
include "wss.mm"
include "ovex.mm"
include "rnex.mm"
include "uniex.mm"
include "xpex.mm"
include "ovssunirn.mm"
include "rnss.mm"
include "uniss.mm"
include "mp2b.mm"
include "sstri.mm"
include "elpw.mm"
include "mpbir.mm"
include "a1i.mm"
include "fmpti.mm"
include "pwex.mm"
include "elmap.mm"
include "rgen2w.mm"
include "fmpt2.mm"
include "mpbi.mm"
include "xpss12.mm"
include "mp2an.mm"
include "elpm2r.mm"
include "mp4an.mm"
include "sbcth.mm"
include "sbcel1g.mm"
include "mpbid.mm"
include "ax-mp.mm"
include "wunf.mm"
include "wuntp.mm"
include "eqeltrd.mm"
include "fuccat.mm"
include "elind.mm"
include "eleqtrrd.mm"

theorem catcfuccl
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cQ: class Q
  let cU: class U
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vv: setvar v
  let vx: setvar x
  assume catcfuccl.c: |- C = ( CatCat ` U )
  assume catcfuccl.b: |- B = ( Base ` C )
  assume catcfuccl.o: |- Q = ( X FuncCat Y )
  assume catcfuccl.u: |- ( ph -> U e. WUni )
  assume catcfuccl.1: |- ( ph -> _om e. U )
  assume catcfuccl.x: |- ( ph -> X e. B )
  assume catcfuccl.y: |- ( ph -> Y e. B )


  assert |- ( ph -> Q e. B )

  proof
    wph
    cQ
    cU
    ccat
    cin
    #
    cB
    wph
    cU
    ccat
    cQ
    wph
    cQ
    cnx
    cbs
    cfv
    #
    cX
    cY
    cfunc
    co
    #
    cop
    #
    cnx
    chom
    cfv
    #
    cX
    cY
    cnat
    co
    #
    cop
    #
    cnx
    cco
    cfv
    #
    vv
    vh
    @2
    @2
    cxp
    #
    @2
    vf
    vv
    cv
    #
    c1st
    cfv
    #
    vg
    @9
    c2nd
    cfv
    #
    vb
    va
    vg
    cv
    #
    vh
    cv
    #
    @5
    co
    #
    vf
    cv
    #
    @12
    @5
    co
    #
    vx
    cX
    cbs
    cfv
    #
    vx
    cv
    #
    vb
    cv
    cfv
    #
    @18
    va
    cv
    cfv
    #
    @18
    @15
    c1st
    cfv
    cfv
    @18
    @12
    c1st
    cfv
    cfv
    cop
    #
    @18
    @13
    c1st
    cfv
    cfv
    #
    cY
    cco
    cfv
    #
    co
    #
    co
    #
    cmpt
    #
    cmpt2
    #
    csb
    #
    csb
    #
    cmpt2
    #
    cop
    #
    ctp
    cU
    wph
    vx
    vv
    @17
    @2
    cX
    cY
    cQ
    @30
    @23
    vf
    vg
    vh
    @5
    va
    vb
    catcfuccl.o
    @2
    eqid
    @5
    eqid
    @17
    eqid
    @23
    eqid
    wph
    @0
    ccat
    cX
    cU
    ccat
    inss2
    #
    wph
    cX
    cB
    @0
    catcfuccl.x
    wph
    cB
    cC
    cU
    cwun
    catcfuccl.c
    catcfuccl.b
    catcfuccl.u
    catcbas
    #
    eleqtrd
    #
    sseldi
    #
    wph
    @0
    ccat
    cY
    @32
    wph
    cY
    cB
    @0
    catcfuccl.y
    @33
    eleqtrd
    #
    sseldi
    #
    wph
    @30
    eqidd
    fucval
    wph
    @3
    @6
    @31
    cU
    catcfuccl.u
    wph
    @1
    @2
    cU
    catcfuccl.u
    wph
    cnx
    cU
    cbs
    c1
    df-base
    catcfuccl.u
    wph
    cU
    catcfuccl.u
    catcfuccl.1
    wunndx
    #
    wunstr
    wph
    cX
    cY
    cU
    catcfuccl.u
    wph
    @0
    cU
    cX
    cU
    ccat
    inss1
    #
    @34
    sseldi
    #
    wph
    @0
    cU
    cY
    @39
    @36
    sseldi
    #
    wunfunc
    #
    wunop
    wph
    @4
    @5
    cU
    catcfuccl.u
    wph
    cnx
    cU
    chom
    c1
    c4
    cdc
    df-hom
    catcfuccl.u
    @38
    wunstr
    wph
    cX
    cY
    cU
    catcfuccl.u
    @40
    @41
    wunnat
    #
    wunop
    wph
    @7
    @30
    cU
    catcfuccl.u
    wph
    cnx
    cU
    cco
    c1
    c5
    cdc
    #
    df-cco
    catcfuccl.u
    @38
    wunstr
    wph
    @8
    @2
    cxp
    #
    @23
    crn
    #
    cuni
    #
    crn
    #
    cuni
    #
    cpw
    #
    @17
    cmap
    co
    #
    @5
    crn
    #
    cuni
    #
    @53
    cxp
    #
    cpm
    co
    #
    cU
    @30
    catcfuccl.u
    wph
    @8
    @2
    cU
    catcfuccl.u
    wph
    @2
    @2
    cU
    catcfuccl.u
    @42
    @42
    wunxp
    @42
    wunxp
    wph
    @51
    @54
    cU
    catcfuccl.u
    wph
    @50
    @17
    cU
    catcfuccl.u
    wph
    @49
    cU
    catcfuccl.u
    wph
    @48
    cU
    catcfuccl.u
    wph
    @47
    cU
    catcfuccl.u
    wph
    @46
    cU
    catcfuccl.u
    wph
    @23
    cU
    catcfuccl.u
    wph
    cY
    cU
    cco
    @44
    df-cco
    catcfuccl.u
    @41
    wunstr
    wunrn
    wununi
    wunrn
    wununi
    wunpw
    wph
    cX
    cU
    cbs
    c1
    df-base
    catcfuccl.u
    @40
    wunstr
    wunmap
    wph
    @53
    @53
    cU
    catcfuccl.u
    wph
    @52
    cU
    catcfuccl.u
    wph
    @5
    cU
    catcfuccl.u
    @43
    wunrn
    wununi
    #
    @56
    wunxp
    wunpm
    @45
    @55
    @30
    wf
    #
    wph
    @29
    @55
    wcel
    #
    vh
    @2
    wral
    vv
    @8
    wral
    @57
    @58
    vv
    vh
    @8
    @2
    @10
    cvv
    wcel
    #
    @58
    @9
    c1st
    fvex
    @59
    @28
    @55
    wcel
    #
    vf
    @10
    wsbc
    @58
    @60
    vf
    @10
    cvv
    @11
    cvv
    wcel
    #
    @60
    @9
    c2nd
    fvex
    @61
    @27
    @55
    wcel
    #
    vg
    @11
    wsbc
    @60
    @62
    vg
    @11
    cvv
    @51
    cvv
    wcel
    @54
    cvv
    wcel
    @14
    @16
    cxp
    #
    @51
    @27
    wf
    #
    @63
    @54
    wss
    #
    @62
    @50
    @17
    cmap
    ovex
    @53
    @53
    @52
    @5
    cX
    cY
    cnat
    ovex
    rnex
    uniex
    #
    @66
    xpex
    @26
    @51
    wcel
    #
    va
    @16
    wral
    vb
    @14
    wral
    @64
    @67
    vb
    va
    @14
    @16
    @67
    @17
    @50
    @26
    wf
    vx
    @17
    @50
    @25
    @26
    @26
    eqid
    @25
    @50
    wcel
    #
    @18
    @17
    wcel
    @68
    @25
    @49
    wss
    @25
    @24
    crn
    #
    cuni
    #
    @49
    @24
    @19
    @20
    ovssunirn
    @24
    @47
    wss
    @69
    @48
    wss
    @70
    @49
    wss
    @23
    @21
    @22
    ovssunirn
    @24
    @47
    rnss
    @69
    @48
    uniss
    mp2b
    sstri
    @25
    @49
    @19
    @20
    @24
    ovex
    elpw
    mpbir
    a1i
    fmpti
    @50
    @17
    @26
    @49
    @48
    @47
    @46
    @23
    cY
    cco
    fvex
    rnex
    uniex
    rnex
    uniex
    pwex
    cX
    cbs
    fvex
    elmap
    mpbir
    rgen2w
    vb
    va
    @14
    @16
    @26
    @51
    @27
    @27
    eqid
    fmpt2
    mpbi
    @14
    @53
    wss
    @16
    @53
    wss
    @65
    @5
    @12
    @13
    ovssunirn
    @5
    @15
    @12
    ovssunirn
    @14
    @53
    @16
    @53
    xpss12
    mp2an
    @51
    @54
    @63
    @27
    cvv
    cvv
    elpm2r
    mp4an
    sbcth
    vg
    @11
    @27
    @55
    cvv
    sbcel1g
    mpbid
    ax-mp
    sbcth
    vf
    @10
    @28
    @55
    cvv
    sbcel1g
    mpbid
    ax-mp
    rgen2w
    vv
    vh
    @8
    @2
    @29
    @55
    @30
    @30
    eqid
    fmpt2
    mpbi
    a1i
    wunf
    wunop
    wuntp
    eqeltrd
    wph
    cX
    cY
    cQ
    catcfuccl.o
    @35
    @37
    fuccat
    elind
    @33
    eleqtrrd
end
