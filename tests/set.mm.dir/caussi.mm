include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "cres.mm"
include "cca.mm"
include "cv.mm"
include "cin.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "cdm.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cuz.mm"
include "wral.mm"
include "cz.mm"
include "wrex.mm"
include "crp.mm"
include "wa.mm"
include "wfun.mm"
include "wss.mm"
include "wi.mm"
include "inss1.mm"
include "xpss2.mm"
include "ax-mp.mm"
include "sstr.mm"
include "mpan2.mm"
include "anim2i.mm"
include "a1i.mm"
include "cvv.mm"
include "wb.mm"
include "elfvdm.mm"
include "inex1g.mm"
include "syl.mm"
include "cnex.mm"
include "elpmg.mm"
include "sylancl.mm"
include "3imtr4d.mm"
include "uzid.mm"
include "adantl.mm"
include "simp2.mm"
include "ralimi.mm"
include "weq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "rspcva.mm"
include "syl2an.mm"
include "inss2.mm"
include "simpr.mm"
include "sseldi.mm"
include "sselda.mm"
include "simplr.mm"
include "ovresd.mm"
include "breq1d.mm"
include "biimpd.mm"
include "imdistanda.mm"
include "sseld.mm"
include "anim1d.mm"
include "syld.mm"
include "syldan.mm"
include "anim2d.mm"
include "3anass.mm"
include "3imtr4g.mm"
include "ralimdv.mm"
include "impancom.mm"
include "mpd.mm"
include "ex.mm"
include "reximdva.mm"
include "anim12d.mm"
include "xmetres.mm"
include "iscau2.mm"
include "ssrdv.mm"

theorem caussi
  let cD: class D
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F


  assert |- ( D e. ( *Met ` X ) -> ( Cau ` ( D |` ( Y X. Y ) ) ) C_ ( Cau ` D ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    vf
    cD
    cY
    cY
    cxp
    cres
    #
    cca
    cfv
    #
    cD
    cca
    cfv
    #
    @0
    vf
    cv
    #
    cX
    cY
    cin
    #
    cc
    cpm
    co
    wcel
    #
    vz
    cv
    #
    @4
    cdm
    wcel
    #
    @7
    @4
    cfv
    #
    @5
    wcel
    #
    @9
    vy
    cv
    #
    @4
    cfv
    #
    @1
    co
    #
    vx
    cv
    #
    clt
    wbr
    #
    w3a
    #
    vz
    @11
    cuz
    cfv
    #
    wral
    #
    vy
    cz
    wrex
    #
    vx
    crp
    wral
    #
    wa
    #
    @4
    cX
    cc
    cpm
    co
    wcel
    #
    @8
    @9
    cX
    wcel
    #
    @9
    @12
    cD
    co
    #
    @14
    clt
    wbr
    #
    w3a
    #
    vz
    @17
    wral
    #
    vy
    cz
    wrex
    #
    vx
    crp
    wral
    #
    wa
    @4
    @2
    wcel
    #
    @4
    @3
    wcel
    @0
    @6
    @22
    @20
    @29
    @0
    @4
    wfun
    #
    @4
    cc
    @5
    cxp
    #
    wss
    #
    wa
    #
    @31
    @4
    cc
    cX
    cxp
    #
    wss
    #
    wa
    #
    @6
    @22
    @34
    @37
    wi
    @0
    @33
    @36
    @31
    @33
    @32
    @35
    wss
    #
    @36
    @5
    cX
    wss
    #
    @38
    cX
    cY
    inss1
    #
    @5
    cX
    cc
    xpss2
    ax-mp
    @4
    @32
    @35
    sstr
    mpan2
    anim2i
    a1i
    @0
    @5
    cvv
    wcel
    #
    cc
    cvv
    wcel
    #
    @6
    @34
    wb
    @0
    cX
    cxmt
    cdm
    #
    wcel
    #
    @41
    cD
    cX
    cxmt
    elfvdm
    #
    cX
    cY
    @43
    inex1g
    syl
    cnex
    @5
    cc
    @4
    cvv
    cvv
    elpmg
    sylancl
    @0
    @44
    @42
    @22
    @37
    wb
    @45
    cnex
    cX
    cc
    @4
    @43
    cvv
    elpmg
    sylancl
    3imtr4d
    @0
    @19
    @28
    vx
    crp
    @0
    @18
    @27
    vy
    cz
    @0
    @11
    cz
    wcel
    #
    wa
    #
    @18
    @27
    @47
    @18
    wa
    @12
    @5
    wcel
    #
    @27
    @47
    @11
    @17
    wcel
    #
    @10
    vz
    @17
    wral
    @48
    @18
    @46
    @49
    @0
    @11
    uzid
    adantl
    @16
    @10
    vz
    @17
    @8
    @10
    @15
    simp2
    ralimi
    @10
    @48
    vz
    @11
    @17
    vz
    vy
    weq
    @9
    @12
    @5
    @7
    @11
    @4
    fveq2
    eleq1d
    rspcva
    syl2an
    @47
    @48
    @18
    @27
    @47
    @48
    wa
    #
    @16
    @26
    vz
    @17
    @50
    @8
    @10
    @15
    wa
    #
    wa
    @8
    @23
    @25
    wa
    #
    wa
    @16
    @26
    @50
    @51
    @52
    @8
    @47
    @48
    @12
    cY
    wcel
    #
    @51
    @52
    wi
    @50
    @5
    cY
    @12
    cX
    cY
    inss2
    #
    @47
    @48
    simpr
    sseldi
    @47
    @53
    wa
    #
    @51
    @10
    @25
    wa
    @52
    @55
    @10
    @15
    @25
    @55
    @10
    wa
    #
    @15
    @25
    @56
    @13
    @24
    @14
    clt
    @56
    @9
    @12
    cD
    cY
    @55
    @5
    cY
    @9
    @5
    cY
    wss
    @55
    @54
    a1i
    sselda
    @47
    @53
    @10
    simplr
    ovresd
    breq1d
    biimpd
    imdistanda
    @55
    @10
    @23
    @25
    @55
    @5
    cX
    @9
    @39
    @55
    @40
    a1i
    sseld
    anim1d
    syld
    syldan
    anim2d
    @8
    @10
    @15
    3anass
    @8
    @23
    @25
    3anass
    3imtr4g
    ralimdv
    impancom
    mpd
    ex
    reximdva
    ralimdv
    anim12d
    @0
    @1
    @5
    cxmt
    cfv
    wcel
    @30
    @21
    wb
    cD
    cY
    cX
    xmetres
    vx
    @1
    vy
    vz
    @4
    @5
    iscau2
    syl
    vx
    cD
    vy
    vz
    @4
    cX
    iscau2
    3imtr4d
    ssrdv
end
