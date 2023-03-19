include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cr.mm"
include "ci.mm"
include "cmin.mm"
include "cmul.mm"
include "wa.mm"
include "wrex.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "cnre.mm"
include "recn.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "subcl.mm"
include "syl2an.mm"
include "adantr.mm"
include "adantl.mm"
include "ppncand.mm"
include "readdcl.mm"
include "anidms.mm"
include "eqeltrd.mm"
include "pnncand.mm"
include "a1i.mm"
include "adddid.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "addcld.mm"
include "mulass.mm"
include "mp3an12.mm"
include "syl.mm"
include "c1.mm"
include "cneg.mm"
include "ixi.mm"
include "1re.mm"
include "renegcli.mm"
include "eqeltri.mm"
include "simpr.mm"
include "readdcld.mm"
include "remulcl.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "oveq1.mm"
include "rexbidv.mm"
include "syl5ibrcom.mm"
include "rexlimivv.mm"
include "an4.mm"
include "cc0.mm"
include "resubcl.mm"
include "pnpcan.mm"
include "3expb.mm"
include "syl5ib.mm"
include "ancoms.mm"
include "adantrl.mm"
include "adantrr.mm"
include "subdid.mm"
include "nnncan1.mm"
include "3com23.mm"
include "eqtr3d.mm"
include "anim12d.mm"
include "rimul.mm"
include "subeq0.mm"
include "biimpd.mm"
include "3syld.mm"
include "syl5bi.mm"
include "ralrimivva.mm"
include "reu4.mm"
include "sylanbrc.mm"

theorem cju
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( A e. CC -> E! x e. CC ( ( A + x ) e. RR /\ ( _i x. ( A - x ) ) e. RR ) )

  proof
    cA
    cc
    wcel
    #
    cA
    vx
    cv
    #
    caddc
    co
    #
    cr
    wcel
    #
    ci
    cA
    @1
    cmin
    co
    #
    cmul
    co
    #
    cr
    wcel
    #
    wa
    #
    vx
    cc
    wrex
    #
    @7
    cA
    vy
    cv
    #
    caddc
    co
    #
    cr
    wcel
    #
    ci
    cA
    @9
    cmin
    co
    #
    cmul
    co
    #
    cr
    wcel
    #
    wa
    #
    wa
    #
    @1
    @9
    wceq
    #
    wi
    #
    vy
    cc
    wral
    vx
    cc
    wral
    @7
    vx
    cc
    wreu
    @0
    cA
    @9
    ci
    vz
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vz
    cr
    wrex
    vy
    cr
    wrex
    @8
    vy
    vz
    cA
    cnre
    @22
    @8
    vy
    vz
    cr
    cr
    @9
    cr
    wcel
    #
    @19
    cr
    wcel
    #
    wa
    #
    @8
    @22
    @21
    @1
    caddc
    co
    #
    cr
    wcel
    #
    ci
    @21
    @1
    cmin
    co
    #
    cmul
    co
    #
    cr
    wcel
    #
    wa
    #
    vx
    cc
    wrex
    #
    @25
    @9
    @20
    cmin
    co
    #
    cc
    wcel
    #
    @21
    @33
    caddc
    co
    #
    cr
    wcel
    #
    ci
    @21
    @33
    cmin
    co
    #
    cmul
    co
    #
    cr
    wcel
    #
    @32
    @23
    @9
    cc
    wcel
    #
    @20
    cc
    wcel
    #
    @34
    @24
    @9
    recn
    #
    @24
    ci
    cc
    wcel
    #
    @19
    cc
    wcel
    #
    @41
    ax-icn
    @19
    recn
    #
    ci
    @19
    mulcl
    sylancr
    #
    @9
    @20
    subcl
    syl2an
    @25
    @35
    @9
    @9
    caddc
    co
    #
    cr
    @25
    @9
    @20
    @9
    @23
    @40
    @24
    @42
    adantr
    #
    @24
    @41
    @23
    @46
    adantl
    #
    @48
    ppncand
    @23
    @47
    cr
    wcel
    #
    @24
    @23
    @50
    @9
    @9
    readdcl
    anidms
    adantr
    eqeltrd
    @25
    @38
    ci
    ci
    cmul
    co
    #
    @19
    @19
    caddc
    co
    #
    cmul
    co
    #
    cr
    @25
    @38
    ci
    ci
    @52
    cmul
    co
    #
    cmul
    co
    #
    @53
    @25
    @37
    @54
    ci
    cmul
    @25
    @37
    @20
    @20
    caddc
    co
    @54
    @25
    @9
    @20
    @20
    @48
    @49
    @49
    pnncand
    @25
    ci
    @19
    @19
    @43
    @25
    ax-icn
    a1i
    @24
    @44
    @23
    @45
    adantl
    #
    @56
    adddid
    eqtr4d
    oveq2d
    @25
    @52
    cc
    wcel
    #
    @53
    @55
    wceq
    #
    @25
    @19
    @19
    @56
    @56
    addcld
    @43
    @43
    @57
    @58
    ax-icn
    ax-icn
    ci
    ci
    @52
    mulass
    mp3an12
    syl
    eqtr4d
    @25
    @51
    cr
    wcel
    @52
    cr
    wcel
    @53
    cr
    wcel
    @51
    c1
    cneg
    cr
    ixi
    c1
    1re
    renegcli
    eqeltri
    @25
    @19
    @19
    @23
    @24
    simpr
    #
    @59
    readdcld
    @51
    @52
    remulcl
    sylancr
    eqeltrd
    @31
    @36
    @39
    wa
    vx
    @33
    cc
    @1
    @33
    wceq
    #
    @27
    @36
    @30
    @39
    @60
    @26
    @35
    cr
    @1
    @33
    @21
    caddc
    oveq2
    eleq1d
    @60
    @29
    @38
    cr
    @60
    @28
    @37
    ci
    cmul
    @1
    @33
    @21
    cmin
    oveq2
    oveq2d
    eleq1d
    anbi12d
    rspcev
    syl12anc
    @22
    @7
    @31
    vx
    cc
    @22
    @3
    @27
    @6
    @30
    @22
    @2
    @26
    cr
    cA
    @21
    @1
    caddc
    oveq1
    eleq1d
    @22
    @5
    @29
    cr
    @22
    @4
    @28
    ci
    cmul
    cA
    @21
    @1
    cmin
    oveq1
    oveq2d
    eleq1d
    anbi12d
    rexbidv
    syl5ibrcom
    rexlimivv
    syl
    @0
    @18
    vx
    vy
    cc
    cc
    @16
    @3
    @11
    wa
    #
    @6
    @14
    wa
    #
    wa
    #
    @0
    @1
    cc
    wcel
    #
    @40
    wa
    #
    wa
    #
    @17
    @3
    @6
    @11
    @14
    an4
    @66
    @63
    @1
    @9
    cmin
    co
    #
    cr
    wcel
    #
    ci
    @67
    cmul
    co
    #
    cr
    wcel
    #
    wa
    #
    @67
    cc0
    wceq
    #
    @17
    @66
    @61
    @68
    @62
    @70
    @61
    @2
    @10
    cmin
    co
    #
    cr
    wcel
    @66
    @68
    @2
    @10
    resubcl
    @66
    @73
    @67
    cr
    @0
    @64
    @40
    @73
    @67
    wceq
    cA
    @1
    @9
    pnpcan
    3expb
    eleq1d
    syl5ib
    @62
    @13
    @5
    cmin
    co
    #
    cr
    wcel
    #
    @66
    @70
    @14
    @6
    @75
    @13
    @5
    resubcl
    ancoms
    @66
    @74
    @69
    cr
    @66
    ci
    @12
    @4
    cmin
    co
    #
    cmul
    co
    @74
    @69
    @66
    ci
    @12
    @4
    @43
    @66
    ax-icn
    a1i
    @0
    @40
    @12
    cc
    wcel
    @64
    cA
    @9
    subcl
    adantrl
    @0
    @64
    @4
    cc
    wcel
    @40
    cA
    @1
    subcl
    adantrr
    subdid
    @66
    @76
    @67
    ci
    cmul
    @0
    @64
    @40
    @76
    @67
    wceq
    #
    @0
    @40
    @64
    @77
    cA
    @9
    @1
    nnncan1
    3com23
    3expb
    oveq2d
    eqtr3d
    eleq1d
    syl5ib
    anim12d
    @71
    @72
    wi
    @66
    @67
    rimul
    a1i
    @65
    @72
    @17
    wi
    @0
    @65
    @72
    @17
    @1
    @9
    subeq0
    biimpd
    adantl
    3syld
    syl5bi
    ralrimivva
    @7
    @15
    vx
    vy
    cc
    @17
    @3
    @11
    @6
    @14
    @17
    @2
    @10
    cr
    @1
    @9
    cA
    caddc
    oveq2
    eleq1d
    @17
    @5
    @13
    cr
    @17
    @4
    @12
    ci
    cmul
    @1
    @9
    cA
    cmin
    oveq2
    oveq2d
    eleq1d
    anbi12d
    reu4
    sylanbrc
end
