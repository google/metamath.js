include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "df-rab.mm"
include "wi.mm"
include "c0g.mm"
include "clmod.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "eqid.mm"
include "lmod0cl.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "lfl0sc.mm"
include "eqtr4d.mm"
include "sneq.mm"
include "xpeq2d.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "a1d.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "lkrssv.mm"
include "wb.mm"
include "adantr.mm"
include "lkr0f.mm"
include "biimpar.mm"
include "sseq1d.mm"
include "biimpa.mm"
include "eqssd.mm"
include "mpbid.mm"
include "ex.mm"
include "wne.mm"
include "clsh.mm"
include "simprr.mm"
include "lkrshp.mm"
include "syl3anc.mm"
include "simplr.mm"
include "simprl.mm"
include "lshpcmp.mm"
include "eqlkr2.mm"
include "syl121anc.mm"
include "sylbid.mm"
include "pm2.61da2ne.mm"
include "lkrscss.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "biimprcd.mm"
include "syl6.mm"
include "rexlimdv.mm"
include "impbid.mm"
include "pm5.32da.mm"
include "lflvscl.mm"
include "eleq1a.mm"
include "pm4.71rd.mm"
include "rexbidva.mm"
include "r19.42v.mm"
include "syl6rbb.mm"
include "bitrd.mm"
include "abbidv.mm"
include "syl5eq.mm"

theorem lfl1dim
  let wph: wff ph
  let cD: class D
  let c.x: class .x.
  let vg: setvar g
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cK: class K
  let cL: class L
  let cV: class V
  let cW: class W
  assume lfl1dim.v: |- V = ( Base ` W )
  assume lfl1dim.d: |- D = ( Scalar ` W )
  assume lfl1dim.f: |- F = ( LFnl ` W )
  assume lfl1dim.l: |- L = ( LKer ` W )
  assume lfl1dim.k: |- K = ( Base ` D )
  assume lfl1dim.t: |- .x. = ( .r ` D )
  assume lfl1dim.w: |- ( ph -> W e. LVec )
  assume lfl1dim.g: |- ( ph -> G e. F )

  disjoint D k
  disjoint F k
  disjoint G k
  disjoint K k
  disjoint L k
  disjoint V k
  disjoint W k
  disjoint g k
  disjoint g ph
  disjoint k ph
  disjoint .x. k
  assert |- ( ph -> { g e. F | ( L ` G ) C_ ( L ` g ) } = { g | E. k e. K g = ( G oF .x. ( V X. { k } ) ) } )

  proof
    wph
    cG
    cL
    cfv
    #
    vg
    cv
    #
    cL
    cfv
    #
    wss
    #
    vg
    cF
    crab
    @1
    cF
    wcel
    #
    @3
    wa
    #
    vg
    cab
    @1
    cG
    cV
    vk
    cv
    #
    csn
    #
    cxp
    #
    c.x
    cof
    #
    co
    #
    wceq
    #
    vk
    cK
    wrex
    #
    vg
    cab
    @3
    vg
    cF
    df-rab
    wph
    @5
    @12
    vg
    wph
    @5
    @4
    @12
    wa
    #
    @12
    wph
    @4
    @3
    @12
    wph
    @4
    wa
    #
    @3
    @12
    @14
    @3
    @12
    wi
    @1
    cV
    cD
    c0g
    cfv
    #
    csn
    #
    cxp
    #
    cG
    @17
    @14
    @1
    @17
    wceq
    #
    wa
    #
    @12
    @3
    @19
    @15
    cK
    wcel
    #
    @1
    cG
    @17
    @9
    co
    #
    wceq
    #
    @12
    wph
    @20
    @4
    @18
    wph
    cW
    clmod
    wcel
    #
    @20
    wph
    cW
    clvec
    wcel
    #
    @23
    lfl1dim.w
    cW
    lveclmod
    syl
    #
    cD
    cK
    cW
    @15
    lfl1dim.d
    lfl1dim.k
    @15
    eqid
    #
    lmod0cl
    syl
    #
    ad2antrr
    @19
    @1
    @17
    @21
    @14
    @18
    simpr
    @19
    cD
    c.x
    cF
    cG
    cK
    cV
    cW
    @15
    lfl1dim.v
    lfl1dim.d
    lfl1dim.f
    lfl1dim.k
    lfl1dim.t
    @26
    wph
    @23
    @4
    @18
    @25
    ad2antrr
    wph
    cG
    cF
    wcel
    #
    @4
    @18
    lfl1dim.g
    ad2antrr
    lfl0sc
    eqtr4d
    @11
    @22
    vk
    @15
    cK
    @6
    @15
    wceq
    #
    @10
    @21
    @1
    @29
    @8
    @17
    cG
    @9
    @29
    @7
    @16
    cV
    @6
    @15
    sneq
    xpeq2d
    oveq2d
    eqeq2d
    rspcev
    #
    syl2anc
    a1d
    @14
    cG
    @17
    wceq
    #
    wa
    #
    @3
    @12
    @32
    @3
    wa
    #
    @20
    @22
    @12
    wph
    @20
    @4
    @31
    @3
    @27
    ad3antrrr
    @33
    @1
    @17
    @21
    @33
    @2
    cV
    wceq
    #
    @18
    @33
    @2
    cV
    @33
    cF
    @1
    cL
    cV
    cW
    lfl1dim.v
    lfl1dim.f
    lfl1dim.l
    wph
    @23
    @4
    @31
    @3
    @25
    ad3antrrr
    #
    wph
    @4
    @31
    @3
    simpllr
    #
    lkrssv
    @32
    @3
    cV
    @2
    wss
    @32
    @0
    cV
    @2
    @14
    @0
    cV
    wceq
    #
    @31
    @14
    @23
    @28
    @37
    @31
    wb
    wph
    @23
    @4
    @25
    adantr
    wph
    @28
    @4
    lfl1dim.g
    adantr
    cD
    cF
    cG
    cL
    cV
    cW
    @15
    lfl1dim.d
    @26
    lfl1dim.v
    lfl1dim.f
    lfl1dim.l
    lkr0f
    syl2anc
    biimpar
    sseq1d
    biimpa
    eqssd
    @33
    @23
    @4
    @34
    @18
    wb
    @35
    @36
    cD
    cF
    @1
    cL
    cV
    cW
    @15
    lfl1dim.d
    @26
    lfl1dim.v
    lfl1dim.f
    lfl1dim.l
    lkr0f
    syl2anc
    mpbid
    @33
    cD
    c.x
    cF
    cG
    cK
    cV
    cW
    @15
    lfl1dim.v
    lfl1dim.d
    lfl1dim.f
    lfl1dim.k
    lfl1dim.t
    @26
    @35
    wph
    @28
    @4
    @31
    @3
    lfl1dim.g
    ad3antrrr
    lfl0sc
    eqtr4d
    @30
    syl2anc
    ex
    @14
    @1
    @17
    wne
    #
    cG
    @17
    wne
    #
    wa
    #
    wa
    #
    @3
    @0
    @2
    wceq
    #
    @12
    @41
    @0
    @2
    cW
    clsh
    cfv
    #
    cW
    @43
    eqid
    #
    wph
    @24
    @4
    @40
    lfl1dim.w
    ad2antrr
    #
    @41
    @24
    @28
    @39
    @0
    @43
    wcel
    @45
    wph
    @28
    @4
    @40
    lfl1dim.g
    ad2antrr
    @14
    @38
    @39
    simprr
    cD
    cF
    cG
    @43
    cL
    cV
    cW
    @15
    lfl1dim.v
    lfl1dim.d
    @26
    @44
    lfl1dim.f
    lfl1dim.l
    lkrshp
    syl3anc
    @41
    @24
    @4
    @38
    @2
    @43
    wcel
    @45
    wph
    @4
    @40
    simplr
    @14
    @38
    @39
    simprl
    cD
    cF
    @1
    @43
    cL
    cV
    cW
    @15
    lfl1dim.v
    lfl1dim.d
    @26
    @44
    lfl1dim.f
    lfl1dim.l
    lkrshp
    syl3anc
    lshpcmp
    @41
    @42
    @12
    @41
    @42
    wa
    @24
    @28
    @4
    @42
    @12
    wph
    @24
    @4
    @40
    @42
    lfl1dim.w
    ad3antrrr
    wph
    @28
    @4
    @40
    @42
    lfl1dim.g
    ad3antrrr
    wph
    @4
    @40
    @42
    simpllr
    @41
    @42
    simpr
    cD
    c.x
    cF
    cG
    @1
    cK
    cL
    cV
    cW
    vk
    lfl1dim.d
    lfl1dim.k
    lfl1dim.t
    lfl1dim.v
    lfl1dim.f
    lfl1dim.l
    eqlkr2
    syl121anc
    ex
    sylbid
    pm2.61da2ne
    @14
    @11
    @3
    vk
    cK
    @14
    @6
    cK
    wcel
    #
    @0
    @10
    cL
    cfv
    #
    wss
    #
    @11
    @3
    wi
    @14
    @46
    @48
    @14
    @46
    wa
    cD
    @6
    c.x
    cF
    cG
    cK
    cL
    cV
    cW
    lfl1dim.v
    lfl1dim.d
    lfl1dim.k
    lfl1dim.t
    lfl1dim.f
    lfl1dim.l
    wph
    @24
    @4
    @46
    lfl1dim.w
    ad2antrr
    wph
    @28
    @4
    @46
    lfl1dim.g
    ad2antrr
    @14
    @46
    simpr
    lkrscss
    ex
    @11
    @3
    @48
    @11
    @2
    @47
    @0
    @1
    @10
    cL
    fveq2
    sseq2d
    biimprcd
    syl6
    rexlimdv
    impbid
    pm5.32da
    wph
    @12
    @4
    @11
    wa
    #
    vk
    cK
    wrex
    @13
    wph
    @11
    @49
    vk
    cK
    wph
    @46
    wa
    #
    @11
    @4
    @50
    @10
    cF
    wcel
    @11
    @4
    wi
    @50
    cD
    @6
    c.x
    cF
    cG
    cK
    cV
    cW
    lfl1dim.v
    lfl1dim.d
    lfl1dim.k
    lfl1dim.t
    lfl1dim.f
    wph
    @23
    @46
    @25
    adantr
    wph
    @28
    @46
    lfl1dim.g
    adantr
    wph
    @46
    simpr
    lflvscl
    @10
    cF
    @1
    eleq1a
    syl
    pm4.71rd
    rexbidva
    @4
    @11
    vk
    cK
    r19.42v
    syl6rbb
    bitrd
    abbidv
    syl5eq
end
