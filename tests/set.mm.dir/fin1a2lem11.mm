include "crpss.mm"
include "wor.mm"
include "cfn.mm"
include "wss.mm"
include "wa.mm"
include "com.mm"
include "cv.mm"
include "cdom.mm"
include "wbr.mm"
include "crab.mm"
include "cuni.mm"
include "cmpt.mm"
include "crn.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "eqid.mm"
include "rnmpt.mm"
include "wcel.mm"
include "wo.mm"
include "unieq.mm"
include "uni0.mm"
include "syl6eq.mm"
include "adantl.mm"
include "0ex.mm"
include "elsn2.mm"
include "sylibr.mm"
include "olcd.mm"
include "wne.mm"
include "ssrab2.mm"
include "simpr.mm"
include "simplll.mm"
include "simpllr.mm"
include "simplr.mm"
include "fin1a2lem9.mm"
include "syl3anc.mm"
include "soss.mm"
include "mpsyl.mm"
include "fin1a2lem10.mm"
include "sseldi.mm"
include "orcd.mm"
include "pm2.61dane.mm"
include "eleq1.mm"
include "orbi12d.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "ccrd.mm"
include "cfv.mm"
include "sselda.mm"
include "ficardom.mm"
include "syl.mm"
include "cen.mm"
include "ficardid.mm"
include "ensym.mm"
include "endom.mm"
include "3syl.mm"
include "breq1.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "elssuni.mm"
include "wral.mm"
include "simprr.mm"
include "adantr.mm"
include "domentr.mm"
include "syl2anc.mm"
include "wb.mm"
include "simprl.mm"
include "sseldd.mm"
include "sorpssi.mm"
include "syl12anc.mm"
include "fincssdom.mm"
include "mpbid.mm"
include "ex.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "unissb.mm"
include "eqssd.mm"
include "breq2.mm"
include "rabbidv.mm"
include "unieqd.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "velsn.mm"
include "peano1.mm"
include "wi.mm"
include "dom0.mm"
include "biimpi.mm"
include "a1i.mm"
include "3imtr4g.mm"
include "ssrdv.mm"
include "uni0b.mm"
include "eqcomd.mm"
include "sylancr.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "jaod.mm"
include "impbid.mm"
include "elun.mm"
include "syl6bbr.mm"
include "abbi1dv.mm"
include "syl5eq.mm"

theorem fin1a2lem11
  let cA: class A
  let vb: setvar b
  let vc: setvar c
  let va: setvar a
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cV: class V
  let cX: class X
  let cC: class C

  disjoint b c
  disjoint A b
  disjoint A c
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b x
  disjoint b y
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c x
  disjoint c y
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint d h
  disjoint d x
  disjoint d y
  disjoint A d
  disjoint e f
  disjoint e g
  disjoint e h
  disjoint e x
  disjoint e y
  disjoint A e
  disjoint f g
  disjoint f h
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint g h
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint h x
  disjoint h y
  disjoint A h
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B d
  disjoint B e
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint V c
  disjoint V x
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint C e
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint C x
  assert |- ( ( [C.] Or A /\ A C_ Fin ) -> ran ( b e. _om |-> U. { c e. A | c ~<_ b } ) = ( A u. { (/) } ) )

  proof
    cA
    crpss
    wor
    #
    cA
    cfn
    wss
    #
    wa
    #
    vb
    com
    vc
    cv
    #
    vb
    cv
    #
    cdom
    wbr
    #
    vc
    cA
    crab
    #
    cuni
    #
    cmpt
    #
    crn
    vd
    cv
    #
    @7
    wceq
    #
    vb
    com
    wrex
    #
    vd
    cab
    cA
    c0
    csn
    #
    cun
    #
    vb
    vd
    com
    @7
    @8
    @8
    eqid
    rnmpt
    @2
    @11
    vd
    @13
    @2
    @11
    @9
    cA
    wcel
    #
    @9
    @12
    wcel
    #
    wo
    #
    @9
    @13
    wcel
    @2
    @11
    @16
    @2
    @10
    @16
    vb
    com
    @2
    @4
    com
    wcel
    #
    wa
    #
    @16
    @10
    @7
    cA
    wcel
    #
    @7
    @12
    wcel
    #
    wo
    #
    @18
    @21
    @6
    c0
    @18
    @6
    c0
    wceq
    #
    wa
    #
    @20
    @19
    @23
    @7
    c0
    wceq
    #
    @20
    @22
    @24
    @18
    @22
    @7
    c0
    cuni
    c0
    @6
    c0
    unieq
    uni0
    syl6eq
    adantl
    @7
    c0
    0ex
    elsn2
    sylibr
    olcd
    @18
    @6
    c0
    wne
    #
    wa
    #
    @19
    @20
    @26
    @6
    cA
    @7
    @5
    vc
    cA
    ssrab2
    #
    @26
    @25
    @6
    cfn
    wcel
    #
    @6
    crpss
    wor
    #
    @7
    @6
    wcel
    @18
    @25
    simpr
    @26
    @0
    @1
    @17
    @28
    @0
    @1
    @17
    @25
    simplll
    #
    @0
    @1
    @17
    @25
    simpllr
    @2
    @17
    @25
    simplr
    @4
    cA
    vc
    fin1a2lem9
    syl3anc
    @6
    cA
    wss
    @26
    @0
    @29
    @27
    @30
    @6
    cA
    crpss
    soss
    mpsyl
    @6
    fin1a2lem10
    syl3anc
    sseldi
    orcd
    pm2.61dane
    @10
    @14
    @19
    @15
    @20
    @9
    @7
    cA
    eleq1
    @9
    @7
    @12
    eleq1
    orbi12d
    syl5ibrcom
    rexlimdva
    @2
    @14
    @11
    @15
    @2
    @14
    @11
    @2
    @14
    wa
    #
    @9
    ccrd
    cfv
    #
    com
    wcel
    #
    @9
    @3
    @32
    cdom
    wbr
    #
    vc
    cA
    crab
    #
    cuni
    #
    wceq
    #
    @11
    @31
    @9
    cfn
    wcel
    #
    @33
    @2
    cA
    cfn
    @9
    @0
    @1
    simpr
    sselda
    #
    @9
    ficardom
    syl
    @31
    @9
    @36
    @31
    @9
    @35
    wcel
    #
    @9
    @36
    wss
    @31
    @14
    @9
    @32
    cdom
    wbr
    #
    @40
    @2
    @14
    simpr
    @31
    @32
    @9
    cen
    wbr
    #
    @9
    @32
    cen
    wbr
    @41
    @31
    @38
    @42
    @39
    @9
    ficardid
    syl
    #
    @32
    @9
    ensym
    @9
    @32
    endom
    3syl
    @34
    @41
    vc
    @9
    cA
    @3
    @9
    @32
    cdom
    breq1
    elrab
    sylanbrc
    @9
    @35
    elssuni
    syl
    @31
    @4
    @9
    wss
    #
    vb
    @35
    wral
    @36
    @9
    wss
    @31
    @44
    vb
    @35
    @4
    @35
    wcel
    @4
    cA
    wcel
    #
    @4
    @32
    cdom
    wbr
    #
    wa
    #
    @31
    @44
    @34
    @46
    vc
    @4
    cA
    @3
    @4
    @32
    cdom
    breq1
    elrab
    @31
    @47
    @44
    @31
    @47
    wa
    #
    @4
    @9
    cdom
    wbr
    #
    @44
    @48
    @46
    @42
    @49
    @31
    @45
    @46
    simprr
    @31
    @42
    @47
    @43
    adantr
    @4
    @32
    @9
    domentr
    syl2anc
    @48
    @4
    cfn
    wcel
    @38
    @44
    @9
    @4
    wss
    wo
    #
    @49
    @44
    wb
    @48
    cA
    cfn
    @4
    @0
    @1
    @14
    @47
    simpllr
    @31
    @45
    @46
    simprl
    #
    sseldd
    @31
    @38
    @47
    @39
    adantr
    @48
    @0
    @45
    @14
    @50
    @0
    @1
    @14
    @47
    simplll
    @51
    @2
    @14
    @47
    simplr
    cA
    @4
    @9
    sorpssi
    syl12anc
    @4
    @9
    fincssdom
    syl3anc
    mpbid
    ex
    syl5bi
    ralrimiv
    vb
    @35
    @9
    unissb
    sylibr
    eqssd
    @10
    @37
    vb
    @32
    com
    @4
    @32
    wceq
    #
    @7
    @36
    @9
    @52
    @6
    @35
    @52
    @5
    @34
    vc
    cA
    @4
    @32
    @3
    cdom
    breq2
    rabbidv
    unieqd
    eqeq2d
    rspcev
    syl2anc
    ex
    @15
    @9
    c0
    wceq
    #
    @2
    @11
    vd
    c0
    velsn
    @2
    @11
    @53
    c0
    @7
    wceq
    #
    vb
    com
    wrex
    #
    @2
    c0
    com
    wcel
    c0
    @3
    c0
    cdom
    wbr
    #
    vc
    cA
    crab
    #
    cuni
    #
    wceq
    #
    @55
    peano1
    @2
    @58
    c0
    @2
    @57
    @12
    wss
    @58
    c0
    wceq
    @2
    vb
    @57
    @12
    @2
    @45
    @4
    c0
    cdom
    wbr
    #
    wa
    #
    @4
    c0
    wceq
    #
    @4
    @57
    wcel
    @4
    @12
    wcel
    @61
    @62
    wi
    @2
    @60
    @62
    @45
    @60
    @62
    @4
    dom0
    biimpi
    adantl
    a1i
    @56
    @60
    vc
    @4
    cA
    @3
    @4
    c0
    cdom
    breq1
    elrab
    vb
    c0
    velsn
    3imtr4g
    ssrdv
    @57
    uni0b
    sylibr
    eqcomd
    @54
    @59
    vb
    c0
    com
    @62
    @7
    @58
    c0
    @62
    @6
    @57
    @62
    @5
    @56
    vc
    cA
    @4
    c0
    @3
    cdom
    breq2
    rabbidv
    unieqd
    eqeq2d
    rspcev
    sylancr
    @53
    @10
    @54
    vb
    com
    @9
    c0
    @7
    eqeq1
    rexbidv
    syl5ibrcom
    syl5bi
    jaod
    impbid
    @9
    cA
    @12
    elun
    syl6bbr
    abbi1dv
    syl5eq
end
