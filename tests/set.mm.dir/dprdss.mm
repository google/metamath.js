include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "co.mm"
include "wss.mm"
include "csubg.mm"
include "cfv.mm"
include "cmrc.mm"
include "cvv.mm"
include "c0g.mm"
include "ccntz.mm"
include "eqid.mm"
include "cgrp.mm"
include "wcel.mm"
include "dprdgrp.mm"
include "syl.mm"
include "dprddomcld.mm"
include "cv.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "wral.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "fveq2.mm"
include "sseq12d.mm"
include "rspcv.mm"
include "mpan9.mm"
include "3ad2antr1.mm"
include "adantr.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "dprdcntz.mm"
include "cbs.mm"
include "wf.mm"
include "dprdf2.mm"
include "ffvelrnd.mm"
include "subgss.mm"
include "sylc.mm"
include "cntz2ss.mm"
include "syl2anc.mm"
include "sstrd.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "cuni.mm"
include "cin.mm"
include "cacs.mm"
include "cmre.mm"
include "subgacs.mm"
include "acsmre.mm"
include "3syl.mm"
include "ciun.mm"
include "difss.mm"
include "ssralv.mm"
include "mpsyl.mm"
include "ss2iun.mm"
include "wfun.mm"
include "ffun.mm"
include "funiunfv.mm"
include "3sstr3d.mm"
include "cpw.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "mresspw.mm"
include "syl5ss.mm"
include "sspwuni.mm"
include "sylib.mm"
include "mrcssd.mm"
include "ss2in.mm"
include "simpr.mm"
include "dprddisj.mm"
include "sseqtrd.mm"
include "dmdprdd.mm"
include "cgsu.mm"
include "cfsupp.mm"
include "cixp.mm"
include "crab.mm"
include "wrex.mm"
include "a1d.mm"
include "wi.mm"
include "ss2ixp.mm"
include "rabss2.mm"
include "ssrexv.mm"
include "anim12d.mm"
include "wb.mm"
include "fdm.mm"
include "eldprd.mm"
include "3imtr4d.mm"
include "ssrdv.mm"
include "jca.mm"

theorem dprdss
  let wph: wff ph
  let cS: class S
  let cT: class T
  let vk: setvar k
  let cG: class G
  let cI: class I
  let va: setvar a
  let vf: setvar f
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  assume dprdss.1: |- ( ph -> G dom DProd T )
  assume dprdss.2: |- ( ph -> dom T = I )
  assume dprdss.3: |- ( ph -> S : I --> ( SubGrp ` G ) )
  assume dprdss.4: |- ( ( ph /\ k e. I ) -> ( S ` k ) C_ ( T ` k ) )

  disjoint G k
  disjoint k ph
  disjoint S k
  disjoint T k
  disjoint I k
  disjoint a f
  disjoint a h
  disjoint a k
  disjoint a x
  disjoint a y
  disjoint G a
  disjoint f h
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint G f
  disjoint h k
  disjoint h x
  disjoint h y
  disjoint G h
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint a ph
  disjoint ph x
  disjoint ph y
  disjoint S a
  disjoint S f
  disjoint S h
  disjoint S x
  disjoint S y
  disjoint T a
  disjoint T f
  disjoint T h
  disjoint I f
  disjoint I h
  disjoint I x
  disjoint I y
  assert |- ( ph -> ( G dom DProd S /\ ( G DProd S ) C_ ( G DProd T ) ) )

  proof
    wph
    cG
    cS
    cdprd
    cdm
    #
    wbr
    #
    cG
    cS
    cdprd
    co
    #
    cG
    cT
    cdprd
    co
    #
    wss
    wph
    vx
    vy
    cS
    cG
    cI
    cG
    csubg
    cfv
    #
    cmrc
    cfv
    #
    cvv
    cG
    c0g
    cfv
    #
    cG
    ccntz
    cfv
    #
    @7
    eqid
    #
    @6
    eqid
    #
    @5
    eqid
    #
    wph
    cG
    cT
    @0
    wbr
    #
    cG
    cgrp
    wcel
    #
    dprdss.1
    cT
    cG
    dprdgrp
    syl
    #
    wph
    cT
    cG
    cI
    dprdss.1
    dprdss.2
    dprddomcld
    dprdss.3
    wph
    vx
    cv
    #
    cI
    wcel
    #
    vy
    cv
    #
    cI
    wcel
    #
    @14
    @16
    wne
    #
    w3a
    #
    wa
    #
    @14
    cS
    cfv
    #
    @14
    cT
    cfv
    #
    @16
    cS
    cfv
    #
    @7
    cfv
    #
    wph
    @17
    @15
    @21
    @22
    wss
    #
    @18
    wph
    vk
    cv
    #
    cS
    cfv
    #
    @26
    cT
    cfv
    #
    wss
    #
    vk
    cI
    wral
    #
    @15
    @25
    wph
    @29
    vk
    cI
    dprdss.4
    ralrimiva
    #
    @29
    @25
    vk
    @14
    cI
    @26
    @14
    wceq
    @27
    @21
    @28
    @22
    @26
    @14
    cS
    fveq2
    @26
    @14
    cT
    fveq2
    sseq12d
    rspcv
    mpan9
    #
    3ad2antr1
    @20
    @22
    @16
    cT
    cfv
    #
    @7
    cfv
    #
    @24
    @20
    cT
    cG
    cI
    @14
    @16
    @7
    wph
    @11
    @19
    dprdss.1
    adantr
    wph
    cT
    cdm
    cI
    wceq
    #
    @19
    dprdss.2
    adantr
    wph
    @15
    @17
    @18
    simpr1
    wph
    @15
    @17
    @18
    simpr2
    #
    wph
    @15
    @17
    @18
    simpr3
    @8
    dprdcntz
    @20
    @33
    cG
    cbs
    cfv
    #
    wss
    #
    @23
    @33
    wss
    #
    @34
    @24
    wss
    @20
    @33
    @4
    wcel
    @38
    @20
    cI
    @4
    @16
    cT
    wph
    cI
    @4
    cT
    wf
    #
    @19
    wph
    cT
    cG
    cI
    dprdss.1
    dprdss.2
    dprdf2
    #
    adantr
    @36
    ffvelrnd
    @37
    @33
    cG
    @37
    eqid
    #
    subgss
    syl
    @20
    @17
    @30
    @39
    @36
    wph
    @30
    @19
    @31
    adantr
    @29
    @39
    vk
    @16
    cI
    @26
    @16
    wceq
    @27
    @23
    @28
    @33
    @26
    @16
    cS
    fveq2
    @26
    @16
    cT
    fveq2
    sseq12d
    rspcv
    sylc
    @37
    @33
    @23
    cG
    @7
    @42
    @8
    cntz2ss
    syl2anc
    sstrd
    sstrd
    wph
    @15
    wa
    #
    @21
    cS
    cI
    @14
    csn
    #
    cdif
    #
    cima
    cuni
    #
    @5
    cfv
    #
    cin
    #
    @22
    cT
    @45
    cima
    #
    cuni
    #
    @5
    cfv
    #
    cin
    #
    @6
    csn
    @43
    @25
    @47
    @51
    wss
    @48
    @52
    wss
    @32
    @43
    @4
    @46
    @5
    @50
    @37
    @43
    @12
    @4
    @37
    cacs
    cfv
    wcel
    @4
    @37
    cmre
    cfv
    wcel
    #
    wph
    @12
    @15
    @13
    adantr
    @37
    cG
    @42
    subgacs
    @4
    @37
    acsmre
    3syl
    #
    @10
    @43
    vk
    @45
    @27
    ciun
    #
    vk
    @45
    @28
    ciun
    #
    @46
    @50
    @43
    @29
    vk
    @45
    wral
    #
    @55
    @56
    wss
    @45
    cI
    wss
    @43
    @30
    @57
    cI
    @44
    difss
    wph
    @30
    @15
    @31
    adantr
    @29
    vk
    @45
    cI
    ssralv
    mpsyl
    vk
    @45
    @27
    @28
    ss2iun
    syl
    @43
    cI
    @4
    cS
    wf
    #
    cS
    wfun
    @55
    @46
    wceq
    wph
    @58
    @15
    dprdss.3
    adantr
    cI
    @4
    cS
    ffun
    vk
    @45
    cS
    funiunfv
    3syl
    @43
    @40
    cT
    wfun
    @56
    @50
    wceq
    wph
    @40
    @15
    @41
    adantr
    #
    cI
    @4
    cT
    ffun
    vk
    @45
    cT
    funiunfv
    3syl
    3sstr3d
    @43
    @49
    @37
    cpw
    #
    wss
    @50
    @37
    wss
    @43
    @49
    cT
    crn
    #
    @60
    cT
    @45
    imassrn
    @43
    @61
    @4
    @60
    @43
    @40
    @61
    @4
    wss
    @59
    cI
    @4
    cT
    frn
    syl
    @43
    @53
    @4
    @60
    wss
    @54
    @4
    @37
    mresspw
    syl
    sstrd
    syl5ss
    @49
    @37
    sspwuni
    sylib
    mrcssd
    @21
    @22
    @47
    @51
    ss2in
    syl2anc
    @43
    cT
    cG
    cI
    @5
    @14
    @6
    wph
    @11
    @15
    dprdss.1
    adantr
    wph
    @35
    @15
    dprdss.2
    adantr
    wph
    @15
    simpr
    @9
    @10
    dprddisj
    sseqtrd
    dmdprdd
    wph
    va
    @2
    @3
    wph
    @1
    va
    cv
    #
    cG
    vf
    cv
    cgsu
    co
    wceq
    #
    vf
    vh
    cv
    @6
    cfsupp
    wbr
    #
    vh
    vk
    cI
    @27
    cixp
    #
    crab
    #
    wrex
    #
    wa
    #
    @11
    @63
    vf
    @64
    vh
    vk
    cI
    @28
    cixp
    #
    crab
    #
    wrex
    #
    wa
    #
    @62
    @2
    wcel
    #
    @62
    @3
    wcel
    #
    wph
    @1
    @11
    @67
    @71
    wph
    @11
    @1
    dprdss.1
    a1d
    wph
    @65
    @69
    wss
    #
    @66
    @70
    wss
    @67
    @71
    wi
    wph
    @30
    @75
    @31
    vk
    cI
    @27
    @28
    ss2ixp
    syl
    @64
    vh
    @65
    @69
    rabss2
    @63
    vf
    @66
    @70
    ssrexv
    3syl
    anim12d
    wph
    @58
    cS
    cdm
    cI
    wceq
    @73
    @68
    wb
    dprdss.3
    cI
    @4
    cS
    fdm
    @62
    cS
    vf
    vh
    vk
    cG
    cI
    @66
    @6
    @9
    @66
    eqid
    eldprd
    3syl
    wph
    @35
    @74
    @72
    wb
    dprdss.2
    @62
    cT
    vf
    vh
    vk
    cG
    cI
    @70
    @6
    @9
    @70
    eqid
    eldprd
    syl
    3imtr4d
    ssrdv
    jca
end
