include "cupgr.mm"
include "wcel.mm"
include "c2.mm"
include "cwwlksn.mm"
include "co.mm"
include "cv.mm"
include "cwwlksnon.mm"
include "wrex.mm"
include "cs3.mm"
include "wceq.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "chash.mm"
include "wa.mm"
include "wex.mm"
include "cc0.mm"
include "c1.mm"
include "w3a.mm"
include "wb.mm"
include "wwlksnwwlksnon.mm"
include "a1i.mm"
include "elwwlks2on.mm"
include "3expb.mm"
include "2rexbidva.mm"
include "rexcom.mm"
include "cvv.mm"
include "cword.mm"
include "s3cli.mm"
include "wi.mm"
include "simplr.mm"
include "simpr.mm"
include "eqtr4d.mm"
include "breq2d.mm"
include "biimpd.mm"
include "com12.mm"
include "adantr.mm"
include "impcom.mm"
include "simprr.mm"
include "vex.mm"
include "s3fv0.mm"
include "eqcomd.mm"
include "mp1i.mm"
include "fveq1.mm"
include "s3fv1.mm"
include "s3fv2.mm"
include "3jca.mm"
include "adantl.mm"
include "ex.mm"
include "spcimedv.mm"
include "c3.mm"
include "caddc.mm"
include "wlklenvp1.mm"
include "simpl.mm"
include "oveq1.mm"
include "eqtrd.mm"
include "2p1e3.mm"
include "syl6eq.mm"
include "exp32.mm"
include "mpd.mm"
include "imp.mm"
include "eqcom.mm"
include "biimpi.mm"
include "3anim123i.mm"
include "anim12i.mm"
include "wlkpwrd.mm"
include "anim1i.mm"
include "3anass.mm"
include "sylibr.mm"
include "ad2antrr.mm"
include "eqwrds3.mm"
include "syl.mm"
include "mpbird.mm"
include "jctird.mm"
include "exp41.mm"
include "com25.mm"
include "pm2.43i.mm"
include "3imp.mm"
include "exlimdv.mm"
include "impbid.mm"
include "exbidv.mm"
include "pm5.32da.mm"
include "syl5bb.mm"
include "rexbidva.mm"
include "3bitrd.mm"

theorem elwwlks2
  let vf: setvar f
  let cG: class G
  let cV: class V
  let cW: class W
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume elwwlks2.v: |- V = ( Vtx ` G )

  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G f
  disjoint G p
  disjoint a b
  disjoint a c
  disjoint a f
  disjoint a p
  disjoint b c
  disjoint b f
  disjoint b p
  disjoint c f
  disjoint c p
  disjoint f p
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint V f
  disjoint V p
  disjoint W a
  disjoint W b
  disjoint W c
  disjoint W f
  disjoint W p
  assert |- ( G e. UPGraph -> ( W e. ( 2 WWalksN G ) <-> E. a e. V E. b e. V E. c e. V ( W = <" a b c "> /\ E. f E. p ( f ( Walks ` G ) p /\ ( # ` f ) = 2 /\ ( a = ( p ` 0 ) /\ b = ( p ` 1 ) /\ c = ( p ` 2 ) ) ) ) ) )

  proof
    cG
    cupgr
    wcel
    #
    cW
    c2
    cG
    cwwlksn
    co
    wcel
    #
    cW
    va
    cv
    #
    vc
    cv
    #
    c2
    cG
    cwwlksnon
    co
    co
    wcel
    #
    vc
    cV
    wrex
    va
    cV
    wrex
    #
    cW
    @2
    vb
    cv
    #
    @3
    cs3
    #
    wceq
    #
    vf
    cv
    #
    cW
    cG
    cwlks
    cfv
    #
    wbr
    #
    @9
    chash
    cfv
    #
    c2
    wceq
    #
    wa
    #
    vf
    wex
    #
    wa
    #
    vb
    cV
    wrex
    #
    vc
    cV
    wrex
    #
    va
    cV
    wrex
    @8
    @9
    vp
    cv
    #
    @10
    wbr
    #
    @13
    @2
    cc0
    @19
    cfv
    #
    wceq
    #
    @6
    c1
    @19
    cfv
    #
    wceq
    #
    @3
    c2
    @19
    cfv
    #
    wceq
    #
    w3a
    #
    w3a
    #
    vp
    wex
    #
    vf
    wex
    #
    wa
    #
    vc
    cV
    wrex
    vb
    cV
    wrex
    #
    va
    cV
    wrex
    @1
    @5
    wb
    @0
    cG
    c2
    cV
    cW
    va
    vc
    elwwlks2.v
    wwlksnwwlksnon
    a1i
    @0
    @4
    @17
    va
    vc
    cV
    cV
    @0
    @2
    cV
    wcel
    #
    @3
    cV
    wcel
    #
    @4
    @17
    wb
    @2
    @3
    vf
    cG
    cV
    cW
    vb
    elwwlks2.v
    elwwlks2on
    3expb
    2rexbidva
    @0
    @18
    @32
    va
    cV
    @18
    @16
    vc
    cV
    wrex
    vb
    cV
    wrex
    @0
    @33
    wa
    #
    @32
    @16
    vc
    vb
    cV
    cV
    rexcom
    @35
    @16
    @31
    vb
    vc
    cV
    cV
    @35
    @6
    cV
    wcel
    #
    @34
    wa
    #
    wa
    #
    @8
    @15
    @30
    @38
    @8
    wa
    #
    @14
    @29
    vf
    @39
    @14
    @29
    @39
    @28
    @14
    vp
    @7
    cvv
    cword
    #
    @7
    @40
    wcel
    @39
    @2
    @6
    @3
    s3cli
    a1i
    @39
    @19
    @7
    wceq
    #
    wa
    #
    @14
    @28
    @42
    @14
    wa
    @20
    @13
    @27
    @14
    @42
    @20
    @11
    @42
    @20
    wi
    @13
    @42
    @11
    @20
    @42
    @11
    @20
    @42
    cW
    @19
    @9
    @10
    @42
    cW
    @7
    @19
    @38
    @8
    @41
    simplr
    @39
    @41
    simpr
    eqtr4d
    breq2d
    biimpd
    com12
    adantr
    impcom
    @42
    @11
    @13
    simprr
    @42
    @27
    @14
    @41
    @27
    @39
    @41
    @22
    @24
    @26
    @41
    @2
    cc0
    @7
    cfv
    #
    @21
    @2
    cvv
    wcel
    #
    @2
    @43
    wceq
    @41
    va
    vex
    @44
    @43
    @2
    @2
    @6
    @3
    cvv
    s3fv0
    eqcomd
    mp1i
    cc0
    @19
    @7
    fveq1
    eqtr4d
    @41
    @6
    c1
    @7
    cfv
    #
    @23
    @6
    cvv
    wcel
    #
    @6
    @45
    wceq
    @41
    vb
    vex
    @46
    @45
    @6
    @2
    @6
    @3
    cvv
    s3fv1
    eqcomd
    mp1i
    c1
    @19
    @7
    fveq1
    eqtr4d
    @41
    @3
    c2
    @7
    cfv
    #
    @25
    @3
    cvv
    wcel
    #
    @3
    @47
    wceq
    @41
    vc
    vex
    @48
    @47
    @3
    @2
    @6
    @3
    cvv
    s3fv2
    eqcomd
    mp1i
    c2
    @19
    @7
    fveq1
    eqtr4d
    3jca
    adantl
    adantr
    3jca
    ex
    spcimedv
    @39
    @28
    @14
    vp
    @28
    @39
    @14
    @20
    @13
    @27
    @39
    @14
    wi
    #
    @20
    @13
    @27
    @49
    wi
    wi
    @20
    @39
    @13
    @27
    @20
    @14
    @20
    @39
    @13
    @27
    @20
    @14
    wi
    @20
    @39
    wa
    #
    @13
    wa
    #
    @27
    wa
    #
    @20
    @11
    @13
    @52
    @20
    @11
    @52
    @19
    cW
    @9
    @10
    @52
    @19
    @7
    cW
    @52
    @41
    @19
    chash
    cfv
    #
    c3
    wceq
    #
    @21
    @2
    wceq
    #
    @23
    @6
    wceq
    #
    @25
    @3
    wceq
    #
    w3a
    #
    wa
    #
    @51
    @54
    @27
    @58
    @50
    @13
    @54
    @20
    @13
    @54
    wi
    #
    @39
    @20
    @53
    @12
    c1
    caddc
    co
    #
    wceq
    #
    @60
    @19
    @9
    cG
    wlklenvp1
    @20
    @62
    @13
    @54
    @20
    @62
    @13
    wa
    #
    wa
    @53
    c2
    c1
    caddc
    co
    #
    c3
    @63
    @53
    @64
    wceq
    @20
    @63
    @53
    @61
    @64
    @62
    @13
    simpl
    @13
    @61
    @64
    wceq
    @62
    @12
    c2
    c1
    caddc
    oveq1
    adantl
    eqtrd
    adantl
    2p1e3
    syl6eq
    exp32
    mpd
    adantr
    imp
    @22
    @55
    @24
    @56
    @26
    @57
    @22
    @55
    @2
    @21
    eqcom
    biimpi
    @24
    @56
    @6
    @23
    eqcom
    biimpi
    @26
    @57
    @3
    @25
    eqcom
    biimpi
    3anim123i
    anim12i
    @52
    @19
    cV
    cword
    wcel
    #
    @33
    @36
    @34
    w3a
    #
    wa
    #
    @41
    @59
    wb
    @50
    @67
    @13
    @27
    @20
    @65
    @39
    @66
    @19
    @9
    cG
    cV
    elwwlks2.v
    wlkpwrd
    @38
    @66
    @8
    @38
    @33
    @37
    wa
    @66
    @35
    @33
    @37
    @0
    @33
    simpr
    anim1i
    @33
    @36
    @34
    3anass
    sylibr
    adantr
    anim12i
    ad2antrr
    @2
    @6
    @3
    cV
    @19
    eqwrds3
    syl
    mpbird
    @50
    @8
    @13
    @27
    @20
    @38
    @8
    simprr
    ad2antrr
    eqtr4d
    breq2d
    biimpd
    @50
    @13
    @27
    simplr
    jctird
    exp41
    com25
    pm2.43i
    3imp
    com12
    exlimdv
    impbid
    exbidv
    pm5.32da
    2rexbidva
    syl5bb
    rexbidva
    3bitrd
end
