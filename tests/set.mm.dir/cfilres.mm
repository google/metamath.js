include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cfil.mm"
include "w3a.mm"
include "ccfil.mm"
include "crest.mm"
include "co.mm"
include "cxp.mm"
include "cres.mm"
include "wa.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "cdif.mm"
include "wn.mm"
include "cfbas.mm"
include "simp2.mm"
include "filfbas.mm"
include "syl.mm"
include "simp3.mm"
include "fbncp.mm"
include "syl2anc.mm"
include "wss.mm"
include "wb.mm"
include "filelss.mm"
include "3adant1.mm"
include "trfil3.mm"
include "mpbird.mm"
include "adantr.mm"
include "cfili.mm"
include "adantll.mm"
include "cin.mm"
include "simpll2.mm"
include "simpll3.mm"
include "jca.mm"
include "elrestr.mm"
include "3expa.mm"
include "sylan.mm"
include "wi.mm"
include "inss1.mm"
include "ssralv.mm"
include "ralimdv.mm"
include "syld.mm"
include "ax-mp.mm"
include "inss2.mm"
include "sseli.mm"
include "ovres.mm"
include "breq1d.mm"
include "syl2an.mm"
include "ralbidva.mm"
include "ralbiia.mm"
include "sylibr.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "rspcev.mm"
include "ex.mm"
include "syl2im.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "simp1.mm"
include "xmetres2.mm"
include "iscfil2.mm"
include "mpbir2and.mm"
include "cfg.mm"
include "cfilresi.mm"
include "3ad2ant1.mm"
include "wceq.mm"
include "fgtr.mm"
include "eleq1d.mm"
include "sylibd.mm"
include "impbid.mm"

theorem cfilres
  let cD: class D
  let cF: class F
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( D e. ( *Met ` X ) /\ F e. ( Fil ` X ) /\ Y e. F ) -> ( F e. ( CauFil ` D ) <-> ( F |`t Y ) e. ( CauFil ` ( D |` ( Y X. Y ) ) ) ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cF
    cX
    cfil
    cfv
    #
    wcel
    #
    cY
    cF
    wcel
    #
    w3a
    #
    cF
    cD
    ccfil
    cfv
    #
    wcel
    #
    cF
    cY
    crest
    co
    #
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
    @4
    @6
    @9
    @4
    @6
    wa
    #
    @9
    @7
    cY
    cfil
    cfv
    wcel
    #
    vu
    cv
    #
    vv
    cv
    #
    @8
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
    #
    vu
    @17
    wral
    #
    vy
    @7
    wrex
    #
    vx
    crp
    wral
    #
    @4
    @11
    @6
    @4
    @11
    cX
    cY
    cdif
    cF
    wcel
    wn
    #
    @4
    cF
    cX
    cfbas
    cfv
    wcel
    #
    @3
    @22
    @4
    @2
    @23
    @0
    @2
    @3
    simp2
    #
    cF
    cX
    filfbas
    syl
    @0
    @2
    @3
    simp3
    cY
    cX
    cF
    cX
    fbncp
    syl2anc
    @4
    @2
    cY
    cX
    wss
    #
    @11
    @22
    wb
    @24
    @2
    @3
    @25
    @0
    cY
    cF
    cX
    filelss
    3adant1
    #
    cY
    cF
    cX
    trfil3
    syl2anc
    mpbird
    adantr
    @10
    @20
    vx
    crp
    @10
    @15
    crp
    wcel
    #
    wa
    #
    @12
    @13
    cD
    co
    #
    @15
    clt
    wbr
    #
    vv
    vs
    cv
    #
    wral
    #
    vu
    @31
    wral
    #
    vs
    cF
    wrex
    #
    @20
    @6
    @27
    @34
    @4
    vs
    vu
    vv
    cD
    @15
    cF
    cfili
    adantll
    @28
    @33
    @20
    vs
    cF
    @28
    @31
    cF
    wcel
    #
    wa
    @31
    cY
    cin
    #
    @7
    wcel
    #
    @33
    @16
    vv
    @36
    wral
    #
    vu
    @36
    wral
    #
    @20
    @28
    @2
    @3
    wa
    @35
    @37
    @28
    @2
    @3
    @0
    @2
    @3
    @6
    @27
    simpll2
    @0
    @2
    @3
    @6
    @27
    simpll3
    jca
    @2
    @3
    @35
    @37
    @31
    cY
    cF
    @1
    cF
    elrestr
    3expa
    sylan
    @33
    @30
    vv
    @36
    wral
    #
    vu
    @36
    wral
    #
    @39
    @36
    @31
    wss
    #
    @33
    @41
    wi
    @31
    cY
    inss1
    @42
    @33
    @40
    vu
    @31
    wral
    @41
    @42
    @32
    @40
    vu
    @31
    @30
    vv
    @36
    @31
    ssralv
    ralimdv
    @40
    vu
    @36
    @31
    ssralv
    syld
    ax-mp
    @38
    @40
    vu
    @36
    @12
    @36
    wcel
    #
    @16
    @30
    vv
    @36
    @43
    @12
    cY
    wcel
    #
    @13
    cY
    wcel
    #
    @16
    @30
    wb
    @13
    @36
    wcel
    @36
    cY
    @12
    @31
    cY
    inss2
    #
    sseli
    @36
    cY
    @13
    @46
    sseli
    @44
    @45
    wa
    @14
    @29
    @15
    clt
    @12
    @13
    cY
    cY
    cD
    ovres
    breq1d
    syl2an
    ralbidva
    ralbiia
    sylibr
    @37
    @39
    @20
    @19
    @39
    vy
    @36
    @7
    @18
    @38
    vu
    @17
    @36
    @16
    vv
    @17
    @36
    raleq
    raleqbi1dv
    rspcev
    ex
    syl2im
    rexlimdva
    mpd
    ralrimiva
    @10
    @8
    cY
    cxmt
    cfv
    wcel
    #
    @9
    @11
    @21
    wa
    wb
    @4
    @47
    @6
    @4
    @0
    @25
    @47
    @0
    @2
    @3
    simp1
    @26
    cD
    cY
    cX
    xmetres2
    syl2anc
    adantr
    vx
    vy
    vu
    vv
    @8
    @7
    cY
    iscfil2
    syl
    mpbir2and
    ex
    @4
    @9
    cX
    @7
    cfg
    co
    #
    @5
    wcel
    #
    @6
    @0
    @2
    @9
    @49
    wi
    @3
    @0
    @9
    @49
    cD
    @7
    cX
    cY
    cfilresi
    ex
    3ad2ant1
    @4
    @48
    cF
    @5
    @2
    @3
    @48
    cF
    wceq
    @0
    cY
    cF
    cX
    fgtr
    3adant1
    eleq1d
    sylibd
    impbid
end
