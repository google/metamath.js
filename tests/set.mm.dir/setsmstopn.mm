include "cmopn.mm"
include "cfv.mm"
include "cts.mm"
include "ctopn.mm"
include "setsmstset.mm"
include "cbs.mm"
include "cpw.mm"
include "wss.mm"
include "wceq.mm"
include "cdm.mm"
include "wcel.mm"
include "cxmt.mm"
include "crn.mm"
include "cuni.mm"
include "cv.mm"
include "cbl.mm"
include "ctg.mm"
include "df-mopn.mm"
include "dmmptss.mm"
include "sseli.mm"
include "wa.mm"
include "simpr.mm"
include "xmetunirn.mm"
include "sylib.mm"
include "eqid.mm"
include "mopnuni.mm"
include "syl.mm"
include "cxp.mm"
include "cds.mm"
include "cin.mm"
include "cres.mm"
include "dmeqd.mm"
include "dmres.mm"
include "syl6eq.mm"
include "inss1.mm"
include "syl6eqss.mm"
include "dmss.mm"
include "dmxpid.mm"
include "syl6sseq.mm"
include "adantr.mm"
include "eqsstr3d.mm"
include "sspwuni.mm"
include "sylibr.mm"
include "ex.mm"
include "syl5.mm"
include "wn.mm"
include "c0.mm"
include "ndmfv.mm"
include "0ss.mm"
include "pm2.61d1.mm"
include "setsmsbas.mm"
include "pweqd.mm"
include "3sstr3d.mm"
include "topnid.mm"
include "eqtrd.mm"

theorem setsmstopn
  let wph: wff ph
  let cD: class D
  let cK: class K
  let cM: class M
  let cV: class V
  let cX: class X
  let vx: setvar x
  assume setsms.x: |- ( ph -> X = ( Base ` M ) )
  assume setsms.d: |- ( ph -> D = ( ( dist ` M ) |` ( X X. X ) ) )
  assume setsms.k: |- ( ph -> K = ( M sSet <. ( TopSet ` ndx ) , ( MetOpen ` D ) >. ) )
  assume setsms.m: |- ( ph -> M e. V )


  assert |- ( ph -> ( MetOpen ` D ) = ( TopOpen ` K ) )

  proof
    wph
    cD
    cmopn
    cfv
    #
    cK
    cts
    cfv
    #
    cK
    ctopn
    cfv
    #
    wph
    cD
    cK
    cM
    cV
    cX
    setsms.x
    setsms.d
    setsms.k
    setsms.m
    setsmstset
    #
    wph
    @1
    cK
    cbs
    cfv
    #
    cpw
    #
    wss
    @1
    @2
    wceq
    wph
    @0
    cX
    cpw
    #
    @1
    @5
    wph
    cD
    cmopn
    cdm
    #
    wcel
    #
    @0
    @6
    wss
    #
    @8
    cD
    cxmt
    crn
    cuni
    #
    wcel
    #
    wph
    @9
    @7
    @10
    cD
    vx
    @10
    vx
    cv
    cbl
    cfv
    crn
    ctg
    cfv
    cmopn
    vx
    df-mopn
    dmmptss
    sseli
    wph
    @11
    @9
    wph
    @11
    wa
    #
    @0
    cuni
    #
    cX
    wss
    @9
    @12
    @13
    cD
    cdm
    #
    cdm
    #
    cX
    @12
    cD
    @15
    cxmt
    cfv
    wcel
    #
    @15
    @13
    wceq
    @12
    @11
    @16
    wph
    @11
    simpr
    cD
    xmetunirn
    sylib
    cD
    @0
    @15
    @0
    eqid
    mopnuni
    syl
    wph
    @15
    cX
    wss
    @11
    wph
    @15
    cX
    cX
    cxp
    #
    cdm
    #
    cX
    wph
    @14
    @17
    wss
    @15
    @18
    wss
    wph
    @14
    @17
    cM
    cds
    cfv
    #
    cdm
    #
    cin
    #
    @17
    wph
    @14
    @19
    @17
    cres
    #
    cdm
    @21
    wph
    cD
    @22
    setsms.d
    dmeqd
    @19
    @17
    dmres
    syl6eq
    @17
    @20
    inss1
    syl6eqss
    @14
    @17
    dmss
    syl
    cX
    dmxpid
    syl6sseq
    adantr
    eqsstr3d
    @0
    cX
    sspwuni
    sylibr
    ex
    syl5
    @8
    wn
    @0
    c0
    @6
    cD
    cmopn
    ndmfv
    @6
    0ss
    syl6eqss
    pm2.61d1
    @3
    wph
    cX
    @4
    wph
    cD
    cK
    cM
    cX
    setsms.x
    setsms.d
    setsms.k
    setsmsbas
    pweqd
    3sstr3d
    @4
    @1
    cK
    @4
    eqid
    @1
    eqid
    topnid
    syl
    eqtrd
end
