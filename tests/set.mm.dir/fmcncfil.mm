include "cms.mm"
include "cfv.mm"
include "wcel.mm"
include "cxmt.mm"
include "ccn.mm"
include "co.mm"
include "w3a.mm"
include "ccfil.mm"
include "wa.mm"
include "cv.mm"
include "cfm.mm"
include "cflim.mm"
include "wex.mm"
include "simpl2.mm"
include "cflf.mm"
include "wi.mm"
include "wal.mm"
include "simpl1.mm"
include "c0.mm"
include "wne.mm"
include "cmetcvg.mm"
include "n0.mm"
include "sylib.mm"
include "sylancom.mm"
include "wral.mm"
include "cfil.mm"
include "cme.mm"
include "cmetmet.mm"
include "metxmet.mm"
include "3syl.mm"
include "cfilfil.mm"
include "ctopon.mm"
include "mopntopon.mm"
include "syl.mm"
include "simpl3.mm"
include "wf.mm"
include "cnflf.mm"
include "simplbda.mm"
include "syl21anc.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq1d.mm"
include "eleq2d.mm"
include "raleqbidv.mm"
include "rspcv.mm"
include "sylc.mm"
include "df-ral.mm"
include "19.29r.mm"
include "pm3.35.mm"
include "eximi.mm"
include "syl2anc.mm"
include "clt.mm"
include "wbr.mm"
include "crp.mm"
include "wrex.mm"
include "metcn.mm"
include "biimpa.mm"
include "simpld.mm"
include "flfval.mm"
include "syl3anc.mm"
include "exbidv.mm"
include "mpbid.mm"
include "flimcfil.mm"
include "ex.mm"
include "exlimdv.mm"

theorem fmcncfil
  let cB: class B
  let cD: class D
  let cE: class E
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vb: setvar b
  let ve: setvar e
  let vx: setvar x
  let vy: setvar y
  let vd: setvar d
  assume fmcncfil.1: |- J = ( MetOpen ` D )
  assume fmcncfil.2: |- K = ( MetOpen ` E )


  assert |- ( ( ( D e. ( CMet ` X ) /\ E e. ( *Met ` Y ) /\ F e. ( J Cn K ) ) /\ B e. ( CauFil ` D ) ) -> ( ( Y FilMap F ) ` B ) e. ( CauFil ` E ) )

  proof
    cD
    cX
    cms
    cfv
    wcel
    #
    cE
    cY
    cxmt
    cfv
    wcel
    #
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    w3a
    #
    cB
    cD
    ccfil
    cfv
    wcel
    #
    wa
    #
    @1
    vx
    cv
    #
    cF
    cfv
    #
    cK
    cB
    cY
    cF
    cfm
    co
    cfv
    #
    cflim
    co
    #
    wcel
    #
    vx
    wex
    #
    @8
    cE
    ccfil
    cfv
    wcel
    #
    @0
    @1
    @2
    @4
    simpl2
    #
    @5
    @7
    cF
    cK
    cB
    cflf
    co
    #
    cfv
    #
    wcel
    #
    vx
    wex
    #
    @11
    @5
    @6
    cJ
    cB
    cflim
    co
    #
    wcel
    #
    vx
    wex
    #
    @19
    @16
    wi
    #
    vx
    wal
    #
    @17
    @3
    @4
    @0
    @20
    @0
    @1
    @2
    @4
    simpl1
    #
    @0
    @4
    wa
    @18
    c0
    wne
    @20
    cD
    cB
    cJ
    cX
    fmcncfil.1
    cmetcvg
    vx
    @18
    n0
    sylib
    sylancom
    @5
    @16
    vx
    @18
    wral
    #
    @22
    @5
    cB
    cX
    cfil
    cfv
    #
    wcel
    #
    @7
    cF
    cK
    vb
    cv
    #
    cflf
    co
    #
    cfv
    #
    wcel
    #
    vx
    cJ
    @27
    cflim
    co
    #
    wral
    #
    vb
    @25
    wral
    #
    @24
    @3
    @4
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @26
    @5
    @0
    cD
    cX
    cme
    cfv
    wcel
    @34
    @23
    cD
    cX
    cmetmet
    cD
    cX
    metxmet
    3syl
    #
    cD
    cB
    cX
    cfilfil
    sylancom
    #
    @5
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    @2
    @33
    @5
    @34
    @37
    @35
    cD
    cJ
    cX
    fmcncfil.1
    mopntopon
    syl
    @5
    @1
    @38
    @13
    cE
    cK
    cY
    fmcncfil.2
    mopntopon
    syl
    #
    @0
    @1
    @2
    @4
    simpl3
    #
    @37
    @38
    wa
    @2
    cX
    cY
    cF
    wf
    #
    @33
    vx
    vb
    cF
    cJ
    cK
    cX
    cY
    cnflf
    simplbda
    syl21anc
    @32
    @24
    vb
    cB
    @25
    @27
    cB
    wceq
    #
    @30
    @16
    vx
    @31
    @18
    @27
    cB
    cJ
    cflim
    oveq2
    @42
    @29
    @15
    @7
    @42
    cF
    @28
    @14
    @27
    cB
    cK
    cflf
    oveq2
    fveq1d
    eleq2d
    raleqbidv
    rspcv
    sylc
    @16
    vx
    @18
    df-ral
    sylib
    @20
    @22
    wa
    @19
    @21
    wa
    #
    vx
    wex
    @17
    @19
    @21
    vx
    19.29r
    @43
    @16
    vx
    @19
    @16
    pm3.35
    eximi
    syl
    syl2anc
    @5
    @16
    @10
    vx
    @5
    @15
    @9
    @7
    @5
    @38
    @26
    @41
    @15
    @9
    wceq
    @39
    @36
    @5
    @41
    @6
    vy
    cv
    #
    cD
    co
    vd
    cv
    clt
    wbr
    @7
    @44
    cF
    cfv
    cE
    co
    ve
    cv
    clt
    wbr
    wi
    vy
    cX
    wral
    vd
    crp
    wrex
    ve
    crp
    wral
    vx
    cX
    wral
    #
    @5
    @34
    @1
    @2
    @41
    @45
    wa
    #
    @35
    @13
    @40
    @34
    @1
    wa
    @2
    @46
    vx
    ve
    vd
    vy
    cD
    cE
    cF
    cJ
    cK
    cX
    cY
    fmcncfil.1
    fmcncfil.2
    metcn
    biimpa
    syl21anc
    simpld
    cF
    cK
    cB
    cY
    cX
    flfval
    syl3anc
    eleq2d
    exbidv
    mpbid
    @1
    @10
    @12
    vx
    @1
    @10
    @12
    @7
    cE
    @8
    cK
    cY
    fmcncfil.2
    flimcfil
    ex
    exlimdv
    sylc
end
