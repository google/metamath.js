include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "cpw.mm"
include "ccrd.mm"
include "cdm.mm"
include "wa.mm"
include "cv.mm"
include "wpss.mm"
include "wn.mm"
include "wss.mm"
include "crab.mm"
include "wral.mm"
include "wrex.mm"
include "cufil.mm"
include "c0.mm"
include "wne.mm"
include "crpss.mm"
include "wor.mm"
include "w3a.mm"
include "cuni.mm"
include "wi.mm"
include "wal.mm"
include "simpr.mm"
include "rabss.mm"
include "filsspw.mm"
include "selpw.mm"
include "sylibr.mm"
include "a1d.mm"
include "mprgbir.mm"
include "ssnum.mm"
include "sylancl.mm"
include "ssid.mm"
include "jctr.mm"
include "sseq2.mm"
include "elrab.mm"
include "ne0i.mm"
include "syl.mm"
include "adantr.mm"
include "cun.mm"
include "simpr1.mm"
include "ssrab.mm"
include "sylib.mm"
include "simpld.mm"
include "simpr2.mm"
include "simpr3.mm"
include "sorpssun.mm"
include "ralrimivva.mm"
include "filuni.mm"
include "syl3anc.mm"
include "wex.mm"
include "n0.mm"
include "ssel2.mm"
include "simprd.mm"
include "ssuni.mm"
include "sylancom.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "sylc.mm"
include "sylanbrc.mm"
include "alrimiv.mm"
include "zornn0g.mm"
include "ralrab.mm"
include "weq.mm"
include "simpll.mm"
include "sstr2.mm"
include "imim1d.mm"
include "df-pss.mm"
include "simplbi2.mm"
include "necon1bd.mm"
include "a2i.mm"
include "syl6.mm"
include "ralimdv.mm"
include "imp.mm"
include "adantll.mm"
include "isufil2.mm"
include "simplr.mm"
include "jca.mm"
include "syl2anb.mm"
include "reximi2.mm"

theorem filssufilg
  let vf: setvar f
  let cF: class F
  let cX: class X
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x

  disjoint F f
  disjoint X f
  disjoint f g
  disjoint f h
  disjoint f x
  disjoint g h
  disjoint g x
  disjoint F g
  disjoint h x
  disjoint F h
  disjoint F x
  disjoint X g
  disjoint X h
  disjoint X x
  assert |- ( ( F e. ( Fil ` X ) /\ ~P ~P X e. dom card ) -> E. f e. ( UFil ` X ) F C_ f )

  proof
    cF
    cX
    cfil
    cfv
    #
    wcel
    #
    cX
    cpw
    #
    cpw
    #
    ccrd
    cdm
    #
    wcel
    #
    wa
    #
    vf
    cv
    #
    vh
    cv
    #
    wpss
    #
    wn
    #
    vh
    cF
    vg
    cv
    #
    wss
    #
    vg
    @0
    crab
    #
    wral
    #
    vf
    @13
    wrex
    #
    cF
    @7
    wss
    #
    vf
    cX
    cufil
    cfv
    #
    wrex
    @6
    @13
    @4
    wcel
    #
    @13
    c0
    wne
    #
    vx
    cv
    #
    @13
    wss
    #
    @20
    c0
    wne
    #
    @20
    crpss
    wor
    #
    w3a
    #
    @20
    cuni
    #
    @13
    wcel
    #
    wi
    #
    vx
    wal
    #
    @15
    @6
    @5
    @13
    @3
    wss
    #
    @18
    @1
    @5
    simpr
    @29
    @12
    @11
    @3
    wcel
    #
    wi
    vg
    @0
    @12
    vg
    @0
    @3
    rabss
    @11
    @0
    wcel
    #
    @30
    @12
    @31
    @11
    @2
    wss
    @30
    @11
    cX
    filsspw
    vg
    @2
    selpw
    sylibr
    a1d
    mprgbir
    @3
    @13
    ssnum
    sylancl
    @1
    @19
    @5
    @1
    cF
    @13
    wcel
    #
    @19
    @1
    @1
    cF
    cF
    wss
    #
    wa
    @32
    @1
    @33
    cF
    ssid
    jctr
    @12
    @33
    vg
    cF
    @0
    @11
    cF
    cF
    sseq2
    elrab
    sylibr
    @13
    cF
    ne0i
    syl
    adantr
    @1
    @28
    @5
    @1
    @27
    vx
    @1
    @24
    @26
    @1
    @24
    wa
    #
    @25
    @0
    wcel
    #
    cF
    @25
    wss
    #
    @26
    @34
    @20
    @0
    wss
    #
    @22
    @11
    @8
    cun
    @20
    wcel
    #
    vh
    @20
    wral
    vg
    @20
    wral
    #
    @35
    @34
    @37
    @12
    vg
    @20
    wral
    #
    @34
    @21
    @37
    @40
    wa
    @1
    @21
    @22
    @23
    simpr1
    #
    @12
    vg
    @0
    @20
    ssrab
    sylib
    simpld
    @1
    @21
    @22
    @23
    simpr2
    #
    @34
    @23
    @39
    @1
    @21
    @22
    @23
    simpr3
    @23
    @38
    vg
    vh
    @20
    @20
    @20
    @11
    @8
    sorpssun
    ralrimivva
    syl
    vg
    vh
    @20
    cX
    filuni
    syl3anc
    @34
    @21
    @22
    @36
    @41
    @42
    @22
    @8
    @20
    wcel
    #
    vh
    wex
    @21
    @36
    vh
    @20
    n0
    @21
    @43
    @36
    vh
    @21
    @43
    @36
    @21
    @43
    cF
    @8
    wss
    #
    @36
    @21
    @43
    wa
    #
    @8
    @0
    wcel
    #
    @44
    @45
    @8
    @13
    wcel
    @46
    @44
    wa
    @20
    @13
    @8
    ssel2
    @12
    @44
    vg
    @8
    @0
    @11
    @8
    cF
    sseq2
    #
    elrab
    sylib
    simprd
    cF
    @8
    @20
    ssuni
    sylancom
    ex
    exlimdv
    syl5bi
    sylc
    @12
    @36
    vg
    @25
    @0
    @11
    @25
    cF
    sseq2
    elrab
    sylanbrc
    ex
    alrimiv
    adantr
    vf
    vh
    vx
    @13
    zornn0g
    syl3anc
    @14
    @16
    vf
    @13
    @17
    @7
    @13
    wcel
    @7
    @0
    wcel
    #
    @16
    wa
    #
    @44
    @10
    wi
    #
    vh
    @0
    wral
    #
    @7
    @17
    wcel
    #
    @16
    wa
    @14
    @12
    @16
    vg
    @7
    @0
    @11
    @7
    cF
    sseq2
    elrab
    @12
    @44
    @10
    vh
    vg
    @0
    @47
    ralrab
    @49
    @51
    wa
    #
    @52
    @16
    @53
    @48
    @7
    @8
    wss
    #
    vf
    vh
    weq
    #
    wi
    #
    vh
    @0
    wral
    #
    @52
    @48
    @16
    @51
    simpll
    @16
    @51
    @57
    @48
    @16
    @51
    @57
    @16
    @50
    @56
    vh
    @0
    @16
    @50
    @54
    @10
    wi
    @56
    @16
    @54
    @44
    @10
    cF
    @7
    @8
    sstr2
    imim1d
    @54
    @10
    @55
    @54
    @9
    @7
    @8
    @9
    @54
    @7
    @8
    wne
    @7
    @8
    df-pss
    simplbi2
    necon1bd
    a2i
    syl6
    ralimdv
    imp
    adantll
    vh
    @7
    cX
    isufil2
    sylanbrc
    @48
    @16
    @51
    simplr
    jca
    syl2anb
    reximi2
    syl
end
