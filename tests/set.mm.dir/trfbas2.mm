include "cfbas.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "c0.mm"
include "wnel.mm"
include "wn.mm"
include "cvv.mm"
include "cpw.mm"
include "wne.mm"
include "cv.mm"
include "cin.mm"
include "wral.mm"
include "wb.mm"
include "cdm.mm"
include "elfvdm.mm"
include "ssexg.mm"
include "ancoms.mm"
include "sylan.mm"
include "restsspw.mm"
include "a1i.mm"
include "wex.mm"
include "fbasne0.mm"
include "adantr.mm"
include "n0.mm"
include "sylib.mm"
include "wi.mm"
include "elrestr.mm"
include "3expia.mm"
include "syldan.mm"
include "ne0i.mm"
include "syl6.mm"
include "exlimdv.mm"
include "mpd.mm"
include "wrex.mm"
include "fbasssin.mm"
include "3expb.mm"
include "adantlr.mm"
include "simplll.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "syl3anc.mm"
include "ssrin.mm"
include "ad2antll.mm"
include "vex.mm"
include "inex1.mm"
include "elpw.mm"
include "sylibr.mm"
include "inelcm.mm"
include "syl2anc.mm"
include "rexlimddv.mm"
include "ralrimivva.mm"
include "wceq.mm"
include "elrest.mm"
include "ineq12.mm"
include "inindir.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "ineq2d.mm"
include "neeq1d.mm"
include "adantll.mm"
include "ralxfr2d.mm"
include "mpbird.mm"
include "w3a.mm"
include "isfbas.mm"
include "baibd.mm"
include "3anan32.mm"
include "syl6bb.mm"
include "syl22anc.mm"
include "df-nel.mm"

theorem trfbas2
  let cA: class A
  let cF: class F
  let cY: class Y
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( F e. ( fBas ` Y ) /\ A C_ Y ) -> ( ( F |`t A ) e. ( fBas ` A ) <-> -. (/) e. ( F |`t A ) ) )

  proof
    cF
    cY
    cfbas
    cfv
    #
    wcel
    #
    cA
    cY
    wss
    #
    wa
    #
    cF
    cA
    crest
    co
    #
    cA
    cfbas
    cfv
    wcel
    #
    c0
    @4
    wnel
    #
    c0
    @4
    wcel
    wn
    @3
    cA
    cvv
    wcel
    #
    @4
    cA
    cpw
    wss
    #
    @4
    c0
    wne
    #
    @4
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    cpw
    #
    cin
    #
    c0
    wne
    #
    vy
    @4
    wral
    #
    vx
    @4
    wral
    #
    @5
    @6
    wb
    @1
    cY
    cfbas
    cdm
    #
    wcel
    #
    @2
    @7
    cF
    cY
    cfbas
    elfvdm
    @2
    @19
    @7
    cA
    cY
    @18
    ssexg
    ancoms
    sylan
    #
    @8
    @3
    cA
    cF
    restsspw
    a1i
    @3
    @10
    cF
    wcel
    #
    vx
    wex
    #
    @9
    @3
    cF
    c0
    wne
    #
    @22
    @1
    @23
    @2
    cY
    cF
    fbasne0
    adantr
    vx
    cF
    n0
    sylib
    @3
    @21
    @9
    vx
    @3
    @21
    @10
    cA
    cin
    #
    @4
    wcel
    #
    @9
    @1
    @2
    @7
    @21
    @25
    wi
    @20
    @1
    @7
    @21
    @25
    @10
    cA
    cF
    @0
    cvv
    elrestr
    #
    3expia
    syldan
    @4
    @24
    ne0i
    syl6
    exlimdv
    mpd
    @3
    @17
    @4
    vz
    cv
    #
    vw
    cv
    #
    cin
    #
    cA
    cin
    #
    cpw
    #
    cin
    #
    c0
    wne
    #
    vw
    cF
    wral
    #
    vz
    cF
    wral
    @3
    @33
    vz
    vw
    cF
    cF
    @3
    @27
    cF
    wcel
    #
    @28
    cF
    wcel
    #
    wa
    #
    wa
    #
    @10
    @29
    wss
    #
    @33
    vx
    cF
    @1
    @37
    @39
    vx
    cF
    wrex
    #
    @2
    @1
    @35
    @36
    @40
    vx
    @27
    @28
    cF
    cY
    fbasssin
    3expb
    adantlr
    @38
    @21
    @39
    wa
    #
    wa
    #
    @25
    @24
    @31
    wcel
    #
    @33
    @42
    @1
    @7
    @21
    @25
    @1
    @2
    @37
    @41
    simplll
    @3
    @7
    @37
    @41
    @20
    ad2antrr
    @38
    @21
    @39
    simprl
    @26
    syl3anc
    @42
    @24
    @30
    wss
    #
    @43
    @39
    @44
    @38
    @21
    @10
    @29
    cA
    ssrin
    ad2antll
    @24
    @30
    @10
    cA
    vx
    vex
    inex1
    elpw
    sylibr
    @24
    @4
    @31
    inelcm
    syl2anc
    rexlimddv
    ralrimivva
    @3
    @16
    @34
    vx
    vz
    @27
    cA
    cin
    #
    @4
    cF
    cvv
    @45
    cvv
    wcel
    @3
    @35
    wa
    @27
    cA
    vz
    vex
    inex1
    a1i
    @1
    @2
    @7
    @10
    @4
    wcel
    @10
    @45
    wceq
    #
    vz
    cF
    wrex
    wb
    @20
    vz
    @10
    cA
    cF
    @0
    cvv
    elrest
    syldan
    @3
    @46
    wa
    #
    @15
    @33
    vy
    vw
    @28
    cA
    cin
    #
    @4
    cF
    cvv
    @48
    cvv
    wcel
    @47
    @36
    wa
    @28
    cA
    vw
    vex
    inex1
    a1i
    @3
    @11
    @4
    wcel
    @11
    @48
    wceq
    #
    vw
    cF
    wrex
    wb
    #
    @46
    @1
    @2
    @7
    @50
    @20
    vw
    @11
    cA
    cF
    @0
    cvv
    elrest
    syldan
    adantr
    @46
    @49
    @15
    @33
    wb
    @3
    @46
    @49
    wa
    #
    @14
    @32
    c0
    @51
    @13
    @31
    @4
    @51
    @12
    @30
    @51
    @12
    @45
    @48
    cin
    @30
    @10
    @45
    @11
    @48
    ineq12
    @27
    @28
    cA
    inindir
    syl6eqr
    pweqd
    ineq2d
    neeq1d
    adantll
    ralxfr2d
    ralxfr2d
    mpbird
    @7
    @8
    wa
    #
    @5
    @9
    @17
    wa
    #
    @6
    @52
    @5
    @9
    @6
    @17
    w3a
    #
    @53
    @6
    wa
    @7
    @5
    @8
    @54
    vx
    vy
    cvv
    cA
    @4
    isfbas
    baibd
    @9
    @6
    @17
    3anan32
    syl6bb
    baibd
    syl22anc
    c0
    @4
    df-nel
    syl6bb
end
