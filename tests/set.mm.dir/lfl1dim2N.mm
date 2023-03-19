include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wcel.mm"
include "wa.mm"
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
include "rabbidva.mm"

theorem lfl1dim2N
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
  assert |- ( ph -> { g e. F | ( L ` G ) C_ ( L ` g ) } = { g e. F | E. k e. K g = ( G oF .x. ( V X. { k } ) ) } )

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
    cF
    wph
    @1
    cF
    wcel
    #
    wa
    #
    @3
    @10
    @12
    @3
    @10
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
    @15
    @12
    @1
    @15
    wceq
    #
    wa
    #
    @10
    @3
    @17
    @13
    cK
    wcel
    #
    @1
    cG
    @15
    @7
    co
    #
    wceq
    #
    @10
    wph
    @18
    @11
    @16
    wph
    cW
    clmod
    wcel
    #
    @18
    wph
    cW
    clvec
    wcel
    #
    @21
    lfl1dim.w
    cW
    lveclmod
    syl
    #
    cD
    cK
    cW
    @13
    lfl1dim.d
    lfl1dim.k
    @13
    eqid
    #
    lmod0cl
    syl
    #
    ad2antrr
    @17
    @1
    @15
    @19
    @12
    @16
    simpr
    @17
    cD
    c.x
    cF
    cG
    cK
    cV
    cW
    @13
    lfl1dim.v
    lfl1dim.d
    lfl1dim.f
    lfl1dim.k
    lfl1dim.t
    @24
    wph
    @21
    @11
    @16
    @23
    ad2antrr
    wph
    cG
    cF
    wcel
    #
    @11
    @16
    lfl1dim.g
    ad2antrr
    lfl0sc
    eqtr4d
    @9
    @20
    vk
    @13
    cK
    @4
    @13
    wceq
    #
    @8
    @19
    @1
    @27
    @6
    @15
    cG
    @7
    @27
    @5
    @14
    cV
    @4
    @13
    sneq
    xpeq2d
    oveq2d
    eqeq2d
    rspcev
    #
    syl2anc
    a1d
    @12
    cG
    @15
    wceq
    #
    wa
    #
    @3
    @10
    @30
    @3
    wa
    #
    @18
    @20
    @10
    wph
    @18
    @11
    @29
    @3
    @25
    ad3antrrr
    @31
    @1
    @15
    @19
    @31
    @2
    cV
    wceq
    #
    @16
    @31
    @2
    cV
    @31
    cF
    @1
    cL
    cV
    cW
    lfl1dim.v
    lfl1dim.f
    lfl1dim.l
    wph
    @21
    @11
    @29
    @3
    @23
    ad3antrrr
    #
    wph
    @11
    @29
    @3
    simpllr
    #
    lkrssv
    @30
    @3
    cV
    @2
    wss
    @30
    @0
    cV
    @2
    @12
    @0
    cV
    wceq
    #
    @29
    @12
    @21
    @26
    @35
    @29
    wb
    wph
    @21
    @11
    @23
    adantr
    wph
    @26
    @11
    lfl1dim.g
    adantr
    cD
    cF
    cG
    cL
    cV
    cW
    @13
    lfl1dim.d
    @24
    lfl1dim.v
    lfl1dim.f
    lfl1dim.l
    lkr0f
    syl2anc
    biimpar
    sseq1d
    biimpa
    eqssd
    @31
    @21
    @11
    @32
    @16
    wb
    @33
    @34
    cD
    cF
    @1
    cL
    cV
    cW
    @13
    lfl1dim.d
    @24
    lfl1dim.v
    lfl1dim.f
    lfl1dim.l
    lkr0f
    syl2anc
    mpbid
    @31
    cD
    c.x
    cF
    cG
    cK
    cV
    cW
    @13
    lfl1dim.v
    lfl1dim.d
    lfl1dim.f
    lfl1dim.k
    lfl1dim.t
    @24
    @33
    wph
    @26
    @11
    @29
    @3
    lfl1dim.g
    ad3antrrr
    lfl0sc
    eqtr4d
    @28
    syl2anc
    ex
    @12
    @1
    @15
    wne
    #
    cG
    @15
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
    @10
    @39
    @0
    @2
    cW
    clsh
    cfv
    #
    cW
    @41
    eqid
    #
    wph
    @22
    @11
    @38
    lfl1dim.w
    ad2antrr
    #
    @39
    @22
    @26
    @37
    @0
    @41
    wcel
    @43
    wph
    @26
    @11
    @38
    lfl1dim.g
    ad2antrr
    @12
    @36
    @37
    simprr
    cD
    cF
    cG
    @41
    cL
    cV
    cW
    @13
    lfl1dim.v
    lfl1dim.d
    @24
    @42
    lfl1dim.f
    lfl1dim.l
    lkrshp
    syl3anc
    @39
    @22
    @11
    @36
    @2
    @41
    wcel
    @43
    wph
    @11
    @38
    simplr
    @12
    @36
    @37
    simprl
    cD
    cF
    @1
    @41
    cL
    cV
    cW
    @13
    lfl1dim.v
    lfl1dim.d
    @24
    @42
    lfl1dim.f
    lfl1dim.l
    lkrshp
    syl3anc
    lshpcmp
    @39
    @40
    @10
    @39
    @40
    wa
    @22
    @26
    @11
    @40
    @10
    wph
    @22
    @11
    @38
    @40
    lfl1dim.w
    ad3antrrr
    wph
    @26
    @11
    @38
    @40
    lfl1dim.g
    ad3antrrr
    wph
    @11
    @38
    @40
    simpllr
    @39
    @40
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
    @12
    @9
    @3
    vk
    cK
    @12
    @4
    cK
    wcel
    #
    @0
    @8
    cL
    cfv
    #
    wss
    #
    @9
    @3
    wi
    @12
    @44
    @46
    @12
    @44
    wa
    cD
    @4
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
    @22
    @11
    @44
    lfl1dim.w
    ad2antrr
    wph
    @26
    @11
    @44
    lfl1dim.g
    ad2antrr
    @12
    @44
    simpr
    lkrscss
    ex
    @9
    @3
    @46
    @9
    @2
    @45
    @0
    @1
    @8
    cL
    fveq2
    sseq2d
    biimprcd
    syl6
    rexlimdv
    impbid
    rabbidva
end
