include "cfrgr.mm"
include "wcel.mm"
include "ccycls.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "chash.mm"
include "c4.mm"
include "wceq.mm"
include "wne.mm"
include "wi.mm"
include "cupgr.mm"
include "cusgr.mm"
include "frgrusgr.mm"
include "usgrupgr.mm"
include "syl.mm"
include "w3a.mm"
include "cv.mm"
include "cpr.mm"
include "cedg.mm"
include "cvtx.mm"
include "wrex.mm"
include "eqid.mm"
include "upgr4cycl4dv4e.mm"
include "wss.mm"
include "wreu.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "frgrusgrfrcond.mm"
include "simplrl.mm"
include "necom.mm"
include "biimpi.mm"
include "3ad2ant2.mm"
include "ad2antrl.mm"
include "adantl.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "sneq.mm"
include "difeq2d.mm"
include "preq2.mm"
include "preq1d.mm"
include "sseq1d.mm"
include "reubidv.mm"
include "raleqbidv.mm"
include "rspcv.mm"
include "ad3antrrr.mm"
include "preq2d.mm"
include "sylsyld.mm"
include "prcom.mm"
include "preq1i.mm"
include "sseq1i.mm"
include "reubii.mm"
include "wn.mm"
include "simpl.mm"
include "simpr.mm"
include "simpllr.mm"
include "simplrr.mm"
include "simprr2.mm"
include "4cycl2vnunb.mm"
include "syl113anc.mm"
include "pm2.21d.mm"
include "com12.mm"
include "sylbi.mm"
include "syl6.mm"
include "pm2.43b.mm"
include "expdcom.mm"
include "rexlimdvva.mm"
include "rexlimivv.mm"
include "3exp.mm"
include "com34.mm"
include "com23.mm"
include "mpcom.mm"
include "imp.mm"
include "neqne.mm"
include "pm2.61d1.mm"

theorem n4cyclfrgr
  let cP: class P
  let cF: class F
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vk: setvar k
  let vl: setvar l
  let vx: setvar x


  assert |- ( ( G e. FriendGraph /\ F ( Cycles ` G ) P ) -> ( # ` F ) =/= 4 )

  proof
    cG
    cfrgr
    wcel
    #
    cF
    cP
    cG
    ccycls
    cfv
    wbr
    #
    wa
    cF
    chash
    cfv
    #
    c4
    wceq
    #
    @2
    c4
    wne
    #
    @0
    @1
    @3
    @4
    wi
    #
    cG
    cupgr
    wcel
    #
    @0
    @1
    @5
    wi
    @0
    cG
    cusgr
    wcel
    #
    @6
    cG
    frgrusgr
    cG
    usgrupgr
    syl
    @6
    @1
    @0
    @5
    @6
    @1
    @3
    @0
    @4
    @6
    @1
    @3
    @0
    @4
    wi
    #
    @6
    @1
    @3
    w3a
    va
    cv
    #
    vb
    cv
    #
    cpr
    cG
    cedg
    cfv
    #
    wcel
    @10
    vc
    cv
    #
    cpr
    @11
    wcel
    wa
    #
    @12
    vd
    cv
    #
    cpr
    @11
    wcel
    @14
    @9
    cpr
    @11
    wcel
    wa
    #
    wa
    #
    @9
    @10
    wne
    #
    @9
    @12
    wne
    #
    @9
    @14
    wne
    #
    w3a
    #
    @10
    @12
    wne
    #
    @10
    @14
    wne
    #
    @12
    @14
    wne
    #
    w3a
    #
    wa
    #
    wa
    #
    vd
    cG
    cvtx
    cfv
    #
    wrex
    vc
    @27
    wrex
    #
    vb
    @27
    wrex
    va
    @27
    wrex
    @8
    cP
    @11
    cF
    cG
    @27
    va
    vb
    vc
    vd
    @27
    eqid
    #
    @11
    eqid
    #
    upgr4cycl4dv4e
    @28
    @8
    va
    vb
    @27
    @27
    @9
    @27
    wcel
    #
    @10
    @27
    wcel
    #
    wa
    #
    @26
    @8
    vc
    vd
    @27
    @27
    @0
    @33
    @12
    @27
    wcel
    #
    @14
    @27
    wcel
    #
    wa
    #
    wa
    #
    @26
    @4
    @0
    @7
    vx
    cv
    #
    vk
    cv
    #
    cpr
    #
    @38
    vl
    cv
    #
    cpr
    #
    cpr
    #
    @11
    wss
    #
    vx
    @27
    wreu
    #
    vl
    @27
    @39
    csn
    #
    cdif
    #
    wral
    #
    vk
    @27
    wral
    #
    wa
    @37
    @26
    wa
    #
    @4
    wi
    #
    vx
    vk
    @11
    cG
    @27
    vl
    @29
    @30
    frgrusgrfrcond
    @49
    @51
    @7
    @49
    @50
    @4
    @50
    @49
    @38
    @9
    cpr
    #
    @38
    @12
    cpr
    #
    cpr
    #
    @11
    wss
    #
    vx
    @27
    wreu
    #
    @51
    @50
    @12
    @27
    @9
    csn
    #
    cdif
    #
    wcel
    #
    @49
    @52
    @42
    cpr
    #
    @11
    wss
    #
    vx
    @27
    wreu
    #
    vl
    @58
    wral
    #
    @56
    @50
    @34
    @12
    @9
    wne
    #
    @59
    @33
    @34
    @35
    @26
    simplrl
    @26
    @64
    @37
    @20
    @64
    @16
    @24
    @18
    @17
    @64
    @19
    @18
    @64
    @9
    @12
    necom
    biimpi
    3ad2ant2
    ad2antrl
    adantl
    @12
    @27
    @9
    eldifsn
    sylanbrc
    @31
    @49
    @63
    wi
    @32
    @36
    @26
    @48
    @63
    vk
    @9
    @27
    @39
    @9
    wceq
    #
    @45
    @62
    vl
    @47
    @58
    @65
    @46
    @57
    @27
    @39
    @9
    sneq
    difeq2d
    @65
    @44
    @61
    vx
    @27
    @65
    @43
    @60
    @11
    @65
    @40
    @52
    @42
    @39
    @9
    @38
    preq2
    preq1d
    sseq1d
    reubidv
    raleqbidv
    rspcv
    ad3antrrr
    @62
    @56
    vl
    @12
    @58
    @41
    @12
    wceq
    #
    @61
    @55
    vx
    @27
    @66
    @60
    @54
    @11
    @66
    @42
    @53
    @52
    @41
    @12
    @38
    preq2
    preq2d
    sseq1d
    reubidv
    rspcv
    sylsyld
    @56
    @9
    @38
    cpr
    #
    @53
    cpr
    #
    @11
    wss
    #
    vx
    @27
    wreu
    #
    @51
    @55
    @69
    vx
    @27
    @54
    @68
    @11
    @52
    @67
    @53
    @38
    @9
    prcom
    preq1i
    sseq1i
    reubii
    @50
    @70
    @4
    @50
    @70
    @4
    @50
    @13
    @15
    @32
    @35
    @22
    @70
    wn
    @16
    @13
    @37
    @25
    @13
    @15
    simpl
    ad2antrl
    @16
    @15
    @37
    @25
    @13
    @15
    simpr
    ad2antrl
    @31
    @32
    @36
    @26
    simpllr
    @33
    @34
    @35
    @26
    simplrr
    @26
    @22
    @37
    @21
    @22
    @23
    @20
    @16
    simprr2
    adantl
    vx
    @9
    @10
    @12
    @14
    @11
    @27
    4cycl2vnunb
    syl113anc
    pm2.21d
    com12
    sylbi
    syl6
    pm2.43b
    adantl
    sylbi
    expdcom
    rexlimdvva
    rexlimivv
    syl
    3exp
    com34
    com23
    mpcom
    imp
    @2
    c4
    neqne
    pm2.61d1
end
