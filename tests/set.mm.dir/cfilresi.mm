include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "cres.mm"
include "ccfil.mm"
include "wa.mm"
include "cfg.mm"
include "co.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "cin.mm"
include "xmetres.mm"
include "cfil.mm"
include "iscfil2.mm"
include "simplbda.mm"
include "sylan.mm"
include "wceq.mm"
include "wss.mm"
include "cfilfil.mm"
include "filelss.mm"
include "inss2.mm"
include "syl6ss.mm"
include "sselda.mm"
include "anim12dan.mm"
include "ovres.mm"
include "syl.mm"
include "breq1d.mm"
include "2ralbidva.mm"
include "rexbidva.mm"
include "ralbidv.mm"
include "mpbid.mm"
include "cfbas.mm"
include "wb.mm"
include "cpw.mm"
include "cdm.mm"
include "filfbas.mm"
include "filsspw.mm"
include "inss1.mm"
include "sspwb.mm"
include "mpbi.mm"
include "elfvdm.mm"
include "adantr.mm"
include "fbasweak.mm"
include "syl3anc.mm"
include "fgcfil.mm"
include "syldan.mm"
include "mpbird.mm"

theorem cfilresi
  let cD: class D
  let cF: class F
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( D e. ( *Met ` X ) /\ F e. ( CauFil ` ( D |` ( Y X. Y ) ) ) ) -> ( X filGen F ) e. ( CauFil ` D ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cF
    cD
    cY
    cY
    cxp
    cres
    #
    ccfil
    cfv
    wcel
    #
    wa
    #
    cX
    cF
    cfg
    co
    cD
    ccfil
    cfv
    wcel
    #
    vu
    cv
    #
    vv
    cv
    #
    cD
    co
    #
    vx
    cv
    #
    clt
    wbr
    #
    vv
    vy
    cv
    #
    wral
    vu
    @10
    wral
    #
    vy
    cF
    wrex
    #
    vx
    crp
    wral
    #
    @3
    @5
    @6
    @1
    co
    #
    @8
    clt
    wbr
    #
    vv
    @10
    wral
    vu
    @10
    wral
    #
    vy
    cF
    wrex
    #
    vx
    crp
    wral
    #
    @13
    @0
    @1
    cX
    cY
    cin
    #
    cxmt
    cfv
    wcel
    #
    @2
    @18
    cD
    cY
    cX
    xmetres
    #
    @20
    @2
    cF
    @19
    cfil
    cfv
    wcel
    #
    @18
    vx
    vy
    vu
    vv
    @1
    cF
    @19
    iscfil2
    simplbda
    sylan
    @3
    @17
    @12
    vx
    crp
    @3
    @16
    @11
    vy
    cF
    @3
    @10
    cF
    wcel
    #
    wa
    #
    @15
    @9
    vu
    vv
    @10
    @10
    @24
    @5
    @10
    wcel
    #
    @6
    @10
    wcel
    #
    wa
    wa
    #
    @14
    @7
    @8
    clt
    @27
    @5
    cY
    wcel
    #
    @6
    cY
    wcel
    #
    wa
    @14
    @7
    wceq
    @24
    @25
    @28
    @26
    @29
    @24
    @10
    cY
    @5
    @24
    @10
    @19
    cY
    @3
    @22
    @23
    @10
    @19
    wss
    @0
    @20
    @2
    @22
    @21
    @1
    cF
    @19
    cfilfil
    sylan
    #
    @10
    cF
    @19
    filelss
    sylan
    cX
    cY
    inss2
    syl6ss
    #
    sselda
    @24
    @10
    cY
    @6
    @31
    sselda
    anim12dan
    @5
    @6
    cY
    cY
    cD
    ovres
    syl
    breq1d
    2ralbidva
    rexbidva
    ralbidv
    mpbid
    @0
    @2
    cF
    cX
    cfbas
    cfv
    wcel
    #
    @4
    @13
    wb
    @3
    cF
    @19
    cfbas
    cfv
    wcel
    #
    cF
    cX
    cpw
    #
    wss
    cX
    cxmt
    cdm
    #
    wcel
    #
    @32
    @3
    @22
    @33
    @30
    cF
    @19
    filfbas
    syl
    @3
    cF
    @19
    cpw
    #
    @34
    @3
    @22
    cF
    @37
    wss
    @30
    cF
    @19
    filsspw
    syl
    @19
    cX
    wss
    @37
    @34
    wss
    cX
    cY
    inss1
    @19
    cX
    sspwb
    mpbi
    syl6ss
    @0
    @36
    @2
    cD
    cX
    cxmt
    elfvdm
    adantr
    cF
    @35
    @19
    cX
    fbasweak
    syl3anc
    vx
    vy
    vu
    vv
    cF
    cD
    cX
    fgcfil
    syldan
    mpbird
end
