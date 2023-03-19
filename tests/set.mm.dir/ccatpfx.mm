include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "w3a.mm"
include "cfzo.mm"
include "cpfx.mm"
include "cop.mm"
include "csubstr.mm"
include "cconcat.mm"
include "wfn.mm"
include "wf.mm"
include "pfxcl.mm"
include "3ad2ant1.mm"
include "swrdcl.mm"
include "ccatcl.mm"
include "syl2anc.mm"
include "wrdf.mm"
include "ffn.mm"
include "3syl.mm"
include "caddc.mm"
include "wceq.mm"
include "ccatlen.mm"
include "cmin.mm"
include "simp1.mm"
include "wa.mm"
include "fzass4.mm"
include "biimpri.mm"
include "simpld.mm"
include "3adant1.mm"
include "pfxlen.mm"
include "swrdlen.mm"
include "oveq12d.mm"
include "cc.mm"
include "cz.mm"
include "elfzelz.mm"
include "ad2antrl.mm"
include "zcnd.mm"
include "3impb.mm"
include "ad2antll.mm"
include "pncan3d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "fneq2d.mm"
include "mpbid.mm"
include "pfxfn.mm"
include "3adant2.mm"
include "cv.mm"
include "wo.mm"
include "simpr.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "fzospliti.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "ccatval1.mm"
include "syl3anc.mm"
include "pfxfv.mm"
include "ccatval2.mm"
include "anim1i.mm"
include "ancomd.mm"
include "fzosubel.mm"
include "syl.mm"
include "wb.mm"
include "subidd.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "mpbird.mm"
include "eqeltrd.mm"
include "swrdfv.mm"
include "syldan.mm"
include "elfzoelz.mm"
include "adantl.mm"
include "npcand.mm"
include "fveq2d.mm"
include "3eqtrd.mm"
include "jaodan.mm"
include "simpl3.mm"
include "eqtr4d.mm"
include "eqfnfvd.mm"

theorem ccatpfx
  let cA: class A
  let cS: class S
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vk: setvar k


  assert |- ( ( S e. Word A /\ Y e. ( 0 ... Z ) /\ Z e. ( 0 ... ( # ` S ) ) ) -> ( ( S prefix Y ) ++ ( S substr <. Y , Z >. ) ) = ( S prefix Z ) )

  proof
    cS
    cA
    cword
    #
    wcel
    #
    cY
    cc0
    cZ
    cfz
    co
    wcel
    #
    cZ
    cc0
    cS
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    #
    w3a
    #
    vx
    cc0
    cZ
    cfzo
    co
    #
    cS
    cY
    cpfx
    co
    #
    cS
    cY
    cZ
    cop
    csubstr
    co
    #
    cconcat
    co
    #
    cS
    cZ
    cpfx
    co
    #
    @6
    @10
    cc0
    @10
    chash
    cfv
    #
    cfzo
    co
    #
    wfn
    #
    @10
    @7
    wfn
    @6
    @10
    @0
    wcel
    #
    @13
    cA
    @10
    wf
    @14
    @6
    @8
    @0
    wcel
    #
    @9
    @0
    wcel
    #
    @15
    @1
    @2
    @16
    @5
    cA
    cS
    cY
    pfxcl
    3ad2ant1
    #
    @1
    @2
    @17
    @5
    cA
    cS
    cY
    cZ
    swrdcl
    3ad2ant1
    #
    cA
    @8
    @9
    ccatcl
    syl2anc
    cA
    @10
    wrdf
    @13
    cA
    @10
    ffn
    3syl
    @6
    @13
    @7
    @10
    @6
    @12
    cZ
    cc0
    cfzo
    @6
    @12
    @8
    chash
    cfv
    #
    @9
    chash
    cfv
    #
    caddc
    co
    #
    cZ
    @6
    @16
    @17
    @12
    @22
    wceq
    @18
    @19
    cA
    @8
    @9
    ccatlen
    syl2anc
    @6
    @22
    cY
    cZ
    cY
    cmin
    co
    #
    caddc
    co
    cZ
    @6
    @20
    cY
    @21
    @23
    caddc
    @6
    @1
    cY
    @4
    wcel
    #
    @20
    cY
    wceq
    @1
    @2
    @5
    simp1
    #
    @2
    @5
    @24
    @1
    @2
    @5
    wa
    #
    @24
    cZ
    cY
    @3
    cfz
    co
    wcel
    #
    @24
    @27
    wa
    @26
    cc0
    cY
    cZ
    @3
    fzass4
    biimpri
    simpld
    3adant1
    #
    cA
    cS
    cY
    pfxlen
    syl2anc
    #
    cA
    cS
    cY
    cZ
    swrdlen
    oveq12d
    @6
    cY
    cZ
    @1
    @2
    @5
    cY
    cc
    wcel
    #
    @1
    @26
    wa
    #
    cY
    @2
    cY
    cz
    wcel
    #
    @1
    @5
    cY
    cc0
    cZ
    elfzelz
    #
    ad2antrl
    zcnd
    3impb
    #
    @1
    @2
    @5
    cZ
    cc
    wcel
    @31
    cZ
    @5
    cZ
    cz
    wcel
    @1
    @2
    cZ
    cc0
    @3
    elfzelz
    ad2antll
    zcnd
    3impb
    pncan3d
    eqtrd
    #
    eqtrd
    oveq2d
    fneq2d
    mpbid
    @1
    @5
    @11
    @7
    wfn
    @2
    cS
    cZ
    cA
    pfxfn
    3adant2
    @6
    vx
    cv
    #
    @7
    wcel
    #
    wa
    #
    @36
    @10
    cfv
    #
    @36
    cS
    cfv
    #
    @36
    @11
    cfv
    #
    @6
    @37
    @36
    cc0
    cY
    cfzo
    co
    #
    wcel
    #
    @36
    cY
    cZ
    cfzo
    co
    #
    wcel
    #
    wo
    #
    @39
    @40
    wceq
    #
    @38
    @37
    @32
    @46
    @6
    @37
    simpr
    #
    @6
    @32
    @37
    @2
    @1
    @32
    @5
    @33
    3ad2ant2
    #
    adantr
    @36
    cc0
    cZ
    cY
    fzospliti
    syl2anc
    @6
    @43
    @47
    @45
    @6
    @43
    wa
    #
    @39
    @36
    @8
    cfv
    #
    @40
    @50
    @16
    @17
    @36
    cc0
    @20
    cfzo
    co
    #
    wcel
    #
    @39
    @51
    wceq
    @6
    @16
    @43
    @18
    adantr
    @6
    @17
    @43
    @19
    adantr
    @6
    @53
    @43
    @6
    @52
    @42
    @36
    @6
    @20
    cY
    cc0
    cfzo
    @29
    oveq2d
    eleq2d
    biimpar
    cA
    @8
    @9
    @36
    ccatval1
    syl3anc
    @50
    @1
    @24
    @43
    @51
    @40
    wceq
    @6
    @1
    @43
    @25
    adantr
    @6
    @24
    @43
    @28
    adantr
    @6
    @43
    simpr
    @36
    cY
    cA
    cS
    pfxfv
    syl3anc
    eqtrd
    @6
    @45
    wa
    #
    @39
    @36
    @20
    cmin
    co
    #
    @9
    cfv
    #
    @55
    cY
    caddc
    co
    #
    cS
    cfv
    #
    @40
    @54
    @16
    @17
    @36
    @20
    @22
    cfzo
    co
    #
    wcel
    #
    @39
    @56
    wceq
    @6
    @16
    @45
    @18
    adantr
    @6
    @17
    @45
    @19
    adantr
    @6
    @60
    @45
    @6
    @59
    @44
    @36
    @6
    @20
    cY
    @22
    cZ
    cfzo
    @29
    @35
    oveq12d
    eleq2d
    biimpar
    cA
    @8
    @9
    @36
    ccatval2
    syl3anc
    @6
    @45
    @55
    cc0
    @23
    cfzo
    co
    #
    wcel
    @56
    @58
    wceq
    @54
    @55
    @36
    cY
    cmin
    co
    #
    @61
    @6
    @55
    @62
    wceq
    @45
    @6
    @20
    cY
    @36
    cmin
    @29
    oveq2d
    adantr
    #
    @54
    @62
    @61
    wcel
    #
    @62
    cY
    cY
    cmin
    co
    #
    @23
    cfzo
    co
    #
    wcel
    #
    @54
    @45
    @32
    wa
    @67
    @54
    @32
    @45
    @6
    @32
    @45
    @49
    anim1i
    ancomd
    @36
    cY
    cZ
    cY
    fzosubel
    syl
    @6
    @64
    @67
    wb
    @45
    @6
    @61
    @66
    @62
    @6
    cc0
    @65
    @23
    cfzo
    @2
    @1
    cc0
    @65
    wceq
    @5
    @2
    @65
    cc0
    @2
    cY
    @2
    cY
    @33
    zcnd
    subidd
    eqcomd
    3ad2ant2
    oveq1d
    eleq2d
    adantr
    mpbird
    eqeltrd
    cA
    cS
    cY
    cZ
    @55
    swrdfv
    syldan
    @54
    @57
    @36
    cS
    @54
    @57
    @62
    cY
    caddc
    co
    @36
    @54
    @55
    @62
    cY
    caddc
    @63
    oveq1d
    @54
    @36
    cY
    @45
    @36
    cc
    wcel
    @6
    @45
    @36
    @36
    cY
    cZ
    elfzoelz
    zcnd
    adantl
    @6
    @30
    @45
    @34
    adantr
    npcand
    eqtrd
    fveq2d
    3eqtrd
    jaodan
    syldan
    @38
    @1
    @5
    @37
    @41
    @40
    wceq
    @6
    @1
    @37
    @25
    adantr
    @1
    @2
    @5
    @37
    simpl3
    @48
    @36
    cZ
    cA
    cS
    pfxfv
    syl3anc
    eqtr4d
    eqfnfvd
end
