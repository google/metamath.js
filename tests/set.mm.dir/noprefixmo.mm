include "csur.mm"
include "wss.mm"
include "cv.mm"
include "cdm.mm"
include "wcel.mm"
include "cslt.mm"
include "wbr.mm"
include "wn.mm"
include "csuc.mm"
include "cres.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "cfv.mm"
include "w3a.mm"
include "wrex.mm"
include "wa.mm"
include "weq.mm"
include "wal.mm"
include "wmo.mm"
include "reeanv.mm"
include "cif.mm"
include "simplrr.mm"
include "simplrl.mm"
include "ifcld.mm"
include "iftrue.mm"
include "adantr.mm"
include "simpll.mm"
include "sseldd.mm"
include "wor.mm"
include "sltso.mm"
include "soasym.mm"
include "mpan.mm"
include "syl2anc.mm"
include "impcom.mm"
include "eqnbrtrd.mm"
include "iffalse.mm"
include "sonr.mm"
include "syl.mm"
include "adantl.mm"
include "pm2.61ian.mm"
include "simpl.mm"
include "simpr1.mm"
include "simprl2.mm"
include "simpr2.mm"
include "breq1.mm"
include "notbid.mm"
include "reseq1.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "simprr2.mm"
include "simpr3.mm"
include "eqtr4d.mm"
include "ex.mm"
include "mp3and.mm"
include "fveq1d.mm"
include "simprl1.mm"
include "sucidg.mm"
include "fvresd.mm"
include "simprl3.mm"
include "eqtrd.mm"
include "simprr3.mm"
include "3eqtr3d.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "alrimivv.mm"
include "eqeq2.mm"
include "3anbi3d.mm"
include "rexbidv.mm"
include "dmeq.mm"
include "eleq2d.mm"
include "breq2.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "fveq1.mm"
include "3anbi123d.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "mo4.mm"
include "sylibr.mm"

theorem noprefixmo
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cG: class G
  let cS: class S
  let vy: setvar y
  let vp: setvar p

  disjoint A u
  disjoint A v
  disjoint A x
  disjoint u v
  disjoint u x
  disjoint v x
  disjoint G u
  disjoint G v
  disjoint G x
  disjoint S x
  disjoint S y
  disjoint x y
  disjoint A p
  disjoint A y
  disjoint p u
  disjoint p v
  disjoint p x
  disjoint p y
  disjoint u y
  disjoint v y
  disjoint G p
  disjoint G y
  assert |- ( A C_ No -> E* x E. u e. A ( G e. dom u /\ A. v e. A ( -. v <s u -> ( u |` suc G ) = ( v |` suc G ) ) /\ ( u ` G ) = x ) )

  proof
    cA
    csur
    wss
    #
    cG
    vu
    cv
    #
    cdm
    #
    wcel
    #
    vv
    cv
    #
    @1
    cslt
    wbr
    #
    wn
    #
    @1
    cG
    csuc
    #
    cres
    #
    @4
    @7
    cres
    #
    wceq
    #
    wi
    #
    vv
    cA
    wral
    #
    cG
    @1
    cfv
    #
    vx
    cv
    #
    wceq
    #
    w3a
    #
    vu
    cA
    wrex
    #
    cG
    vp
    cv
    #
    cdm
    #
    wcel
    #
    @4
    @18
    cslt
    wbr
    #
    wn
    #
    @18
    @7
    cres
    #
    @9
    wceq
    #
    wi
    #
    vv
    cA
    wral
    #
    cG
    @18
    cfv
    #
    vy
    cv
    #
    wceq
    #
    w3a
    #
    vp
    cA
    wrex
    #
    wa
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    wal
    vx
    wal
    @17
    vx
    wmo
    @0
    @34
    vx
    vy
    @32
    @16
    @30
    wa
    #
    vp
    cA
    wrex
    vu
    cA
    wrex
    @0
    @33
    @16
    @30
    vu
    vp
    cA
    cA
    reeanv
    @0
    @35
    @33
    vu
    vp
    cA
    cA
    @0
    @1
    cA
    wcel
    #
    @18
    cA
    wcel
    #
    wa
    #
    wa
    #
    @35
    @33
    @39
    @35
    wa
    #
    cG
    @8
    cfv
    #
    cG
    @23
    cfv
    #
    @14
    @28
    @40
    cG
    @8
    @23
    @40
    @1
    @18
    cslt
    wbr
    #
    @18
    @1
    cif
    #
    cA
    wcel
    #
    @44
    @1
    cslt
    wbr
    #
    wn
    #
    @44
    @18
    cslt
    wbr
    #
    wn
    #
    @8
    @23
    wceq
    #
    @40
    @43
    @18
    @1
    cA
    @0
    @36
    @37
    @35
    simplrr
    #
    @0
    @36
    @37
    @35
    simplrl
    #
    ifcld
    @43
    @40
    @47
    @43
    @40
    wa
    #
    @44
    @18
    @1
    cslt
    @43
    @44
    @18
    wceq
    @40
    @43
    @18
    @1
    iftrue
    adantr
    #
    @40
    @43
    @18
    @1
    cslt
    wbr
    wn
    #
    @40
    @1
    csur
    wcel
    #
    @18
    csur
    wcel
    #
    @43
    @55
    wi
    #
    @40
    cA
    csur
    @1
    @0
    @38
    @35
    simpll
    #
    @52
    sseldd
    #
    @40
    cA
    csur
    @18
    @59
    @51
    sseldd
    #
    csur
    cslt
    wor
    #
    @56
    @57
    wa
    @58
    sltso
    csur
    cslt
    @1
    @18
    soasym
    mpan
    syl2anc
    impcom
    eqnbrtrd
    @43
    wn
    #
    @40
    wa
    #
    @44
    @1
    @1
    cslt
    @63
    @44
    @1
    wceq
    @40
    @43
    @18
    @1
    iffalse
    adantr
    #
    @40
    @1
    @1
    cslt
    wbr
    wn
    #
    @63
    @40
    @56
    @66
    @60
    @62
    @56
    @66
    sltso
    csur
    @1
    cslt
    sonr
    mpan
    syl
    adantl
    eqnbrtrd
    pm2.61ian
    @43
    @40
    @49
    @53
    @44
    @18
    @18
    cslt
    @54
    @40
    @18
    @18
    cslt
    wbr
    wn
    #
    @43
    @40
    @57
    @67
    @61
    @62
    @57
    @67
    sltso
    csur
    @18
    cslt
    sonr
    mpan
    syl
    adantl
    eqnbrtrd
    @64
    @44
    @1
    @18
    cslt
    @65
    @63
    @40
    simpl
    eqnbrtrd
    pm2.61ian
    @40
    @45
    @47
    @49
    w3a
    #
    @50
    @40
    @68
    wa
    #
    @8
    @44
    @7
    cres
    #
    @23
    @69
    @45
    @12
    @47
    @8
    @70
    wceq
    #
    @40
    @45
    @47
    @49
    simpr1
    #
    @40
    @12
    @68
    @3
    @12
    @15
    @30
    @39
    simprl2
    adantr
    @40
    @45
    @47
    @49
    simpr2
    @11
    @47
    @71
    wi
    vv
    @44
    cA
    @4
    @44
    wceq
    #
    @6
    @47
    @10
    @71
    @73
    @5
    @46
    @4
    @44
    @1
    cslt
    breq1
    notbid
    @73
    @9
    @70
    @8
    @4
    @44
    @7
    reseq1
    #
    eqeq2d
    imbi12d
    rspcv
    syl3c
    @69
    @45
    @26
    @49
    @23
    @70
    wceq
    #
    @72
    @40
    @26
    @68
    @20
    @26
    @29
    @16
    @39
    simprr2
    adantr
    @40
    @45
    @47
    @49
    simpr3
    @25
    @49
    @75
    wi
    vv
    @44
    cA
    @73
    @22
    @49
    @24
    @75
    @73
    @21
    @48
    @4
    @44
    @18
    cslt
    breq1
    notbid
    @73
    @9
    @70
    @23
    @74
    eqeq2d
    imbi12d
    rspcv
    syl3c
    eqtr4d
    ex
    mp3and
    fveq1d
    @40
    @41
    @13
    @14
    @40
    cG
    @7
    @1
    @40
    @3
    cG
    @7
    wcel
    @3
    @12
    @15
    @30
    @39
    simprl1
    cG
    @2
    sucidg
    syl
    #
    fvresd
    @3
    @12
    @15
    @30
    @39
    simprl3
    eqtrd
    @40
    @42
    @27
    @28
    @40
    cG
    @7
    @18
    @76
    fvresd
    @20
    @26
    @29
    @16
    @39
    simprr3
    eqtrd
    3eqtr3d
    ex
    rexlimdvva
    syl5bir
    alrimivv
    @17
    @31
    vx
    vy
    @33
    @17
    @3
    @12
    @13
    @28
    wceq
    #
    w3a
    #
    vu
    cA
    wrex
    @31
    @33
    @16
    @78
    vu
    cA
    @33
    @15
    @77
    @3
    @12
    @14
    @28
    @13
    eqeq2
    3anbi3d
    rexbidv
    @78
    @30
    vu
    vp
    cA
    vu
    vp
    weq
    #
    @3
    @20
    @12
    @26
    @77
    @29
    @79
    @2
    @19
    cG
    @1
    @18
    dmeq
    eleq2d
    @79
    @11
    @25
    vv
    cA
    @79
    @6
    @22
    @10
    @24
    @79
    @5
    @21
    @1
    @18
    @4
    cslt
    breq2
    notbid
    @79
    @8
    @23
    @9
    @1
    @18
    @7
    reseq1
    eqeq1d
    imbi12d
    ralbidv
    @79
    @13
    @27
    @28
    cG
    @1
    @18
    fveq1
    eqeq1d
    3anbi123d
    cbvrexv
    syl6bb
    mo4
    sylibr
end
