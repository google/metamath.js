include "cfbas.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cvv.mm"
include "cfg.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "wb.mm"
include "cpw.mm"
include "cfil.mm"
include "simpll.mm"
include "fgcl.mm"
include "filfbas.mm"
include "3syl.mm"
include "fbsspw.mm"
include "syl.mm"
include "simplr.mm"
include "sspwb.mm"
include "sylib.mm"
include "sstrd.mm"
include "simpr.mm"
include "fbasweak.mm"
include "syl3anc.mm"
include "elfg.mm"
include "wi.mm"
include "adantr.mm"
include "ad2antrr.mm"
include "ssfg.mm"
include "sselda.mm"
include "adantrr.mm"
include "simplrl.mm"
include "simprlr.mm"
include "simprr.mm"
include "filss.mm"
include "syl13anc.mm"
include "expr.mm"
include "rexlimdvaa.mm"
include "anassrs.mm"
include "expimpd.mm"
include "sylbid.mm"
include "rexlimdv.mm"
include "ssrdv.mm"
include "fgss.mm"
include "eqssd.mm"
include "ex.mm"
include "wn.mm"
include "c0.mm"
include "cin.mm"
include "wne.mm"
include "crab.mm"
include "df-fg.mm"
include "reldmmpt2.mm"
include "ovprc1.mm"
include "eqtr4d.mm"
include "pm2.61d1.mm"

theorem fgabs
  let cF: class F
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( F e. ( fBas ` Y ) /\ Y C_ X ) -> ( X filGen ( Y filGen F ) ) = ( X filGen F ) )

  proof
    cF
    cY
    cfbas
    cfv
    #
    wcel
    #
    cY
    cX
    wss
    #
    wa
    #
    cX
    cvv
    wcel
    #
    cX
    cY
    cF
    cfg
    co
    #
    cfg
    co
    #
    cX
    cF
    cfg
    co
    #
    wceq
    #
    @3
    @4
    @8
    @3
    @4
    wa
    #
    @6
    @7
    @9
    vx
    @6
    @7
    @9
    vx
    cv
    #
    @6
    wcel
    #
    @10
    cX
    wss
    #
    vy
    cv
    #
    @10
    wss
    #
    vy
    @5
    wrex
    #
    wa
    #
    @10
    @7
    wcel
    #
    @9
    @5
    cX
    cfbas
    cfv
    #
    wcel
    #
    @11
    @16
    wb
    @9
    @5
    @0
    wcel
    #
    @5
    cX
    cpw
    #
    wss
    @4
    @19
    @9
    @1
    @5
    cY
    cfil
    cfv
    wcel
    @20
    @1
    @2
    @4
    simpll
    #
    cF
    cY
    fgcl
    @5
    cY
    filfbas
    3syl
    #
    @9
    @5
    cY
    cpw
    #
    @21
    @9
    @20
    @5
    @24
    wss
    @23
    cY
    @5
    fbsspw
    syl
    @9
    @2
    @24
    @21
    wss
    @1
    @2
    @4
    simplr
    cY
    cX
    sspwb
    sylib
    #
    sstrd
    @3
    @4
    simpr
    #
    @5
    cvv
    cY
    cX
    fbasweak
    syl3anc
    #
    vy
    @10
    @5
    cX
    elfg
    syl
    @9
    @12
    @15
    @17
    @9
    @12
    wa
    #
    @14
    @17
    vy
    @5
    @28
    @13
    @5
    wcel
    #
    @13
    cY
    wss
    #
    vz
    cv
    #
    @13
    wss
    #
    vz
    cF
    wrex
    #
    wa
    #
    @14
    @17
    wi
    #
    @28
    @1
    @29
    @34
    wb
    @9
    @1
    @12
    @22
    adantr
    vz
    @13
    cF
    cY
    elfg
    syl
    @28
    @30
    @33
    @35
    @9
    @12
    @30
    @33
    @35
    wi
    @9
    @12
    @30
    wa
    #
    wa
    #
    @32
    @35
    vz
    cF
    @37
    @31
    cF
    wcel
    #
    @32
    wa
    #
    @14
    @17
    @37
    @39
    @14
    wa
    #
    wa
    #
    @7
    cX
    cfil
    cfv
    wcel
    #
    @31
    @7
    wcel
    #
    @12
    @31
    @10
    wss
    @17
    @9
    @42
    @36
    @40
    @9
    cF
    @18
    wcel
    #
    @42
    @9
    @1
    cF
    @21
    wss
    @4
    @44
    @22
    @9
    cF
    @24
    @21
    @9
    @1
    cF
    @24
    wss
    @22
    cY
    cF
    fbsspw
    syl
    @25
    sstrd
    @26
    cF
    cvv
    cY
    cX
    fbasweak
    syl3anc
    #
    cF
    cX
    fgcl
    syl
    ad2antrr
    @37
    @39
    @43
    @14
    @37
    @38
    @43
    @32
    @37
    cF
    @7
    @31
    @9
    cF
    @7
    wss
    #
    @36
    @9
    @44
    @46
    @45
    cF
    cX
    ssfg
    syl
    adantr
    sselda
    adantrr
    adantrr
    @9
    @12
    @30
    @40
    simplrl
    @41
    @31
    @13
    @10
    @37
    @38
    @32
    @14
    simprlr
    @37
    @39
    @14
    simprr
    sstrd
    @31
    @10
    @7
    cX
    filss
    syl13anc
    expr
    rexlimdvaa
    anassrs
    expimpd
    sylbid
    rexlimdv
    expimpd
    sylbid
    ssrdv
    @9
    @44
    @19
    cF
    @5
    wss
    #
    @7
    @6
    wss
    @45
    @27
    @1
    @47
    @2
    @4
    cF
    cY
    ssfg
    ad2antrr
    cF
    @5
    cX
    fgss
    syl3anc
    eqssd
    ex
    @4
    wn
    @6
    c0
    @7
    cX
    @5
    cfg
    vw
    vx
    cvv
    vw
    cv
    #
    cfbas
    cfv
    @10
    @13
    cpw
    cin
    c0
    wne
    vy
    @48
    cpw
    crab
    cfg
    vx
    vy
    vw
    df-fg
    reldmmpt2
    #
    ovprc1
    cX
    cF
    cfg
    @49
    ovprc1
    eqtr4d
    pm2.61d1
end
