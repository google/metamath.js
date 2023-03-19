include "ccat.mm"
include "cin.mm"
include "cnx.mm"
include "chom.mm"
include "cfv.mm"
include "ctpos.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cco.mm"
include "cbs.mm"
include "cxp.mm"
include "cv.mm"
include "c2nd.mm"
include "c1st.mm"
include "cmpt2.mm"
include "wcel.mm"
include "wceq.mm"
include "eqid.mm"
include "oppcval.mm"
include "syl.mm"
include "inss1.mm"
include "cwun.mm"
include "catcbas.mm"
include "eleqtrd.mm"
include "sseldi.mm"
include "c1.mm"
include "c4.mm"
include "cdc.mm"
include "df-hom.mm"
include "wunndx.mm"
include "wunstr.mm"
include "wuntpos.mm"
include "wunop.mm"
include "wunsets.mm"
include "c5.mm"
include "df-cco.mm"
include "crn.mm"
include "cuni.mm"
include "cdm.mm"
include "ccnv.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "cpw.mm"
include "df-base.mm"
include "wunxp.mm"
include "wunrn.mm"
include "wununi.mm"
include "wundm.mm"
include "wuncnv.mm"
include "wun0.mm"
include "wunsn.mm"
include "wunun.mm"
include "wunpw.mm"
include "wral.mm"
include "wf.mm"
include "wss.mm"
include "tposssxp.mm"
include "ovssunirn.mm"
include "dmss.mm"
include "ax-mp.mm"
include "cnvss.mm"
include "unss1.mm"
include "mp2b.mm"
include "rnss.mm"
include "xpss12.mm"
include "mp2an.mm"
include "sstri.mm"
include "wb.mm"
include "elpw2g.mm"
include "mpbiri.mm"
include "ralrimivw.mm"
include "fmpt2.mm"
include "sylib.mm"
include "wunf.mm"
include "eqeltrd.mm"
include "inss2.mm"
include "oppccat.mm"
include "elind.mm"
include "eleqtrrd.mm"

theorem catcoppccl
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cU: class U
  let cO: class O
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume catcoppccl.c: |- C = ( CatCat ` U )
  assume catcoppccl.b: |- B = ( Base ` C )
  assume catcoppccl.o: |- O = ( oppCat ` X )
  assume catcoppccl.1: |- ( ph -> U e. WUni )
  assume catcoppccl.2: |- ( ph -> _om e. U )
  assume catcoppccl.3: |- ( ph -> X e. B )


  assert |- ( ph -> O e. B )

  proof
    wph
    cO
    cU
    ccat
    cin
    #
    cB
    wph
    cU
    ccat
    cO
    wph
    cO
    cX
    cnx
    chom
    cfv
    #
    cX
    chom
    cfv
    #
    ctpos
    #
    cop
    #
    csts
    co
    #
    cnx
    cco
    cfv
    #
    vx
    vy
    cX
    cbs
    cfv
    #
    @7
    cxp
    #
    @7
    vy
    cv
    vx
    cv
    #
    c2nd
    cfv
    cop
    #
    @9
    c1st
    cfv
    #
    cX
    cco
    cfv
    #
    co
    #
    ctpos
    #
    cmpt2
    #
    cop
    #
    csts
    co
    #
    cU
    wph
    cX
    cB
    wcel
    cO
    @17
    wceq
    catcoppccl.3
    vy
    vx
    @7
    cX
    @12
    @2
    cO
    cB
    @7
    eqid
    @2
    eqid
    @12
    eqid
    catcoppccl.o
    oppcval
    syl
    wph
    @16
    @5
    cU
    catcoppccl.1
    wph
    @4
    cX
    cU
    catcoppccl.1
    wph
    @0
    cU
    cX
    cU
    ccat
    inss1
    wph
    cX
    cB
    @0
    catcoppccl.3
    wph
    cB
    cC
    cU
    cwun
    catcoppccl.c
    catcoppccl.b
    catcoppccl.1
    catcbas
    #
    eleqtrd
    #
    sseldi
    #
    wph
    @1
    @3
    cU
    catcoppccl.1
    wph
    cnx
    cU
    chom
    c1
    c4
    cdc
    #
    df-hom
    catcoppccl.1
    wph
    cU
    catcoppccl.1
    catcoppccl.2
    wunndx
    #
    wunstr
    wph
    @2
    cU
    catcoppccl.1
    wph
    cX
    cU
    chom
    @21
    df-hom
    catcoppccl.1
    @20
    wunstr
    wuntpos
    wunop
    wunsets
    wph
    @6
    @15
    cU
    catcoppccl.1
    wph
    cnx
    cU
    cco
    c1
    c5
    cdc
    #
    df-cco
    catcoppccl.1
    @22
    wunstr
    wph
    @8
    @7
    cxp
    #
    @12
    crn
    #
    cuni
    #
    cdm
    #
    ccnv
    #
    c0
    csn
    #
    cun
    #
    @26
    crn
    #
    cxp
    #
    cpw
    #
    cU
    @15
    catcoppccl.1
    wph
    @8
    @7
    cU
    catcoppccl.1
    wph
    @7
    @7
    cU
    catcoppccl.1
    wph
    cX
    cU
    cbs
    c1
    df-base
    catcoppccl.1
    @20
    wunstr
    #
    @34
    wunxp
    @34
    wunxp
    wph
    @32
    cU
    catcoppccl.1
    wph
    @30
    @31
    cU
    catcoppccl.1
    wph
    @28
    @29
    cU
    catcoppccl.1
    wph
    @27
    cU
    catcoppccl.1
    wph
    @26
    cU
    catcoppccl.1
    wph
    @25
    cU
    catcoppccl.1
    wph
    @12
    cU
    catcoppccl.1
    wph
    cX
    cU
    cco
    @23
    df-cco
    catcoppccl.1
    @20
    wunstr
    wunrn
    wununi
    #
    wundm
    wuncnv
    wph
    c0
    cU
    catcoppccl.1
    wph
    cU
    catcoppccl.1
    wun0
    wunsn
    wunun
    wph
    @26
    cU
    catcoppccl.1
    @35
    wunrn
    wunxp
    #
    wunpw
    wph
    @14
    @33
    wcel
    #
    vy
    @7
    wral
    #
    vx
    @8
    wral
    @24
    @33
    @15
    wf
    wph
    @38
    vx
    @8
    wph
    @37
    vy
    @7
    wph
    @37
    @14
    @32
    wss
    #
    @14
    @13
    cdm
    #
    ccnv
    #
    @29
    cun
    #
    @13
    crn
    #
    cxp
    #
    @32
    @13
    tposssxp
    @42
    @30
    wss
    #
    @43
    @31
    wss
    #
    @44
    @32
    wss
    @40
    @27
    wss
    #
    @41
    @28
    wss
    @45
    @13
    @26
    wss
    #
    @47
    @12
    @10
    @11
    ovssunirn
    #
    @13
    @26
    dmss
    ax-mp
    @40
    @27
    cnvss
    @41
    @28
    @29
    unss1
    mp2b
    @48
    @46
    @49
    @13
    @26
    rnss
    ax-mp
    @42
    @30
    @43
    @31
    xpss12
    mp2an
    sstri
    wph
    @32
    cU
    wcel
    @37
    @39
    wb
    @36
    @14
    @32
    cU
    elpw2g
    syl
    mpbiri
    ralrimivw
    ralrimivw
    vx
    vy
    @8
    @7
    @14
    @33
    @15
    @15
    eqid
    fmpt2
    sylib
    wunf
    wunop
    wunsets
    eqeltrd
    wph
    cX
    ccat
    wcel
    cO
    ccat
    wcel
    wph
    @0
    ccat
    cX
    cU
    ccat
    inss2
    @19
    sseldi
    cX
    cO
    catcoppccl.o
    oppccat
    syl
    elind
    @18
    eleqtrrd
end
