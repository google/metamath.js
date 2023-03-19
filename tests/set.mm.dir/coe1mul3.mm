include "caddc.mm"
include "co.mm"
include "cco1.mm"
include "cfv.mm"
include "cn0.mm"
include "cc0.mm"
include "cv.mm"
include "cfz.mm"
include "cmin.mm"
include "cmpt.mm"
include "cgsu.mm"
include "crg.mm"
include "wcel.mm"
include "wceq.mm"
include "coe1mul.mm"
include "syl3anc.mm"
include "fveq1d.mm"
include "nn0addcld.mm"
include "oveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "mpteq12dv.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "cbs.mm"
include "cvv.mm"
include "c0g.mm"
include "cmnd.mm"
include "ringmnd.mm"
include "ovexd.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "nn0red.mm"
include "nn0addge1.mm"
include "syl2anc.mm"
include "wa.mm"
include "wb.mm"
include "fznn0.mm"
include "mpbir2and.mm"
include "adantr.mm"
include "wf.mm"
include "coe1f.mm"
include "elfznn0.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "fznn0sub.mm"
include "ringcl.mm"
include "fmptd.mm"
include "csn.mm"
include "cdif.mm"
include "wne.mm"
include "eldifsn.mm"
include "clt.mm"
include "wo.mm"
include "adantl.mm"
include "lttri2d.mm"
include "ad2antrr.mm"
include "cxr.mm"
include "deg1xrcl.mm"
include "rexrd.mm"
include "resubcld.mm"
include "ltadd1d.mm"
include "ltaddsub2d.mm"
include "bitrd.mm"
include "biimpa.mm"
include "xrlelttrd.mm"
include "deg1lt.mm"
include "ringrz.mm"
include "eqtrd.mm"
include "simpr.mm"
include "oveq1d.mm"
include "ringlz.mm"
include "jaodan.mm"
include "ex.mm"
include "sylbid.mm"
include "impr.mm"
include "sylan2b.mm"
include "suppss2.mm"
include "gsumpt.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "nn0cnd.mm"
include "pncan2d.mm"
include "3eqtrd.mm"

theorem coe1mul3
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cI: class I
  let cJ: class J
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume coe1mul3.s: |- Y = ( Poly1 ` R )
  assume coe1mul3.t: |- .xb = ( .r ` Y )
  assume coe1mul3.u: |- .x. = ( .r ` R )
  assume coe1mul3.b: |- B = ( Base ` Y )
  assume coe1mul3.d: |- D = ( deg1 ` R )
  assume coe1mul3.r: |- ( ph -> R e. Ring )
  assume coe1mul3.f1: |- ( ph -> F e. B )
  assume coe1mul3.f2: |- ( ph -> I e. NN0 )
  assume coe1mul3.f3: |- ( ph -> ( D ` F ) <_ I )
  assume coe1mul3.g1: |- ( ph -> G e. B )
  assume coe1mul3.g2: |- ( ph -> J e. NN0 )
  assume coe1mul3.g3: |- ( ph -> ( D ` G ) <_ J )


  assert |- ( ph -> ( ( coe1 ` ( F .xb G ) ) ` ( I + J ) ) = ( ( ( coe1 ` F ) ` I ) .x. ( ( coe1 ` G ) ` J ) ) )

  proof
    wph
    cI
    cJ
    caddc
    co
    #
    cF
    cG
    c.xb
    co
    cco1
    cfv
    #
    cfv
    @0
    vx
    cn0
    cR
    vy
    cc0
    vx
    cv
    #
    cfz
    co
    #
    vy
    cv
    #
    cF
    cco1
    cfv
    #
    cfv
    #
    @2
    @4
    cmin
    co
    #
    cG
    cco1
    cfv
    #
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    cfv
    #
    cR
    vy
    cc0
    @0
    cfz
    co
    #
    @6
    @0
    @4
    cmin
    co
    #
    @8
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cI
    @5
    cfv
    #
    cJ
    @8
    cfv
    #
    c.x
    co
    #
    wph
    @0
    @1
    @13
    wph
    cR
    crg
    wcel
    #
    cF
    cB
    wcel
    #
    cG
    cB
    wcel
    #
    @1
    @13
    wceq
    coe1mul3.r
    coe1mul3.f1
    coe1mul3.g1
    vy
    cB
    cR
    c.xb
    c.x
    vx
    cF
    cG
    cY
    coe1mul3.s
    coe1mul3.t
    coe1mul3.u
    coe1mul3.b
    coe1mul
    syl3anc
    fveq1d
    wph
    @0
    cn0
    wcel
    #
    @14
    @20
    wceq
    wph
    cI
    cJ
    coe1mul3.f2
    coe1mul3.g2
    nn0addcld
    #
    vx
    @0
    @12
    @20
    cn0
    @13
    @2
    @0
    wceq
    #
    @11
    @19
    cR
    cgsu
    @29
    vy
    @3
    @10
    @15
    @18
    @2
    @0
    cc0
    cfz
    oveq2
    @29
    @9
    @17
    @6
    c.x
    @29
    @7
    @16
    @8
    @2
    @0
    @4
    cmin
    oveq1
    fveq2d
    oveq2d
    mpteq12dv
    oveq2d
    @13
    eqid
    cR
    @19
    cgsu
    ovex
    fvmpt
    syl
    wph
    @20
    cI
    @19
    cfv
    #
    @21
    @0
    cI
    cmin
    co
    #
    @8
    cfv
    #
    c.x
    co
    #
    @23
    wph
    @15
    cR
    cbs
    cfv
    #
    @19
    cR
    cvv
    cI
    cR
    c0g
    cfv
    #
    @34
    eqid
    #
    @35
    eqid
    #
    wph
    @24
    cR
    cmnd
    wcel
    coe1mul3.r
    cR
    ringmnd
    syl
    wph
    cc0
    @0
    cfz
    ovexd
    #
    wph
    cI
    @15
    wcel
    #
    cI
    cn0
    wcel
    #
    cI
    @0
    cle
    wbr
    #
    coe1mul3.f2
    wph
    cI
    cr
    wcel
    #
    cJ
    cn0
    wcel
    @41
    wph
    cI
    coe1mul3.f2
    nn0red
    #
    coe1mul3.g2
    cI
    cJ
    nn0addge1
    syl2anc
    wph
    @27
    @39
    @40
    @41
    wa
    wb
    @28
    cI
    @0
    fznn0
    syl
    mpbir2and
    #
    wph
    vy
    @15
    @18
    @34
    @19
    wph
    @4
    @15
    wcel
    #
    wa
    #
    @24
    @6
    @34
    wcel
    #
    @17
    @34
    wcel
    #
    @18
    @34
    wcel
    wph
    @24
    @45
    coe1mul3.r
    adantr
    #
    wph
    cn0
    @34
    @5
    wf
    #
    @4
    cn0
    wcel
    #
    @47
    @45
    wph
    @25
    @50
    coe1mul3.f1
    @5
    cB
    cY
    cR
    cF
    @34
    @5
    eqid
    #
    coe1mul3.b
    coe1mul3.s
    @36
    coe1f
    syl
    @4
    @0
    elfznn0
    #
    cn0
    @34
    @4
    @5
    ffvelrn
    syl2an
    #
    wph
    cn0
    @34
    @8
    wf
    #
    @16
    cn0
    wcel
    #
    @48
    @45
    wph
    @26
    @55
    coe1mul3.g1
    @8
    cB
    cY
    cR
    cG
    @34
    @8
    eqid
    #
    coe1mul3.b
    coe1mul3.s
    @36
    coe1f
    syl
    @4
    cc0
    @0
    fznn0sub
    #
    cn0
    @34
    @16
    @8
    ffvelrn
    syl2an
    #
    @34
    cR
    c.x
    @6
    @17
    @36
    coe1mul3.u
    ringcl
    syl3anc
    @19
    eqid
    #
    fmptd
    wph
    @15
    @18
    vy
    cvv
    cI
    csn
    #
    @35
    @4
    @15
    @61
    cdif
    wcel
    wph
    @45
    @4
    cI
    wne
    #
    wa
    @18
    @35
    wceq
    #
    @4
    @15
    cI
    eldifsn
    wph
    @45
    @62
    @63
    @46
    @62
    @4
    cI
    clt
    wbr
    #
    cI
    @4
    clt
    wbr
    #
    wo
    #
    @63
    @46
    @4
    cI
    @46
    @4
    @45
    @51
    wph
    @53
    adantl
    #
    nn0red
    #
    wph
    @42
    @45
    @43
    adantr
    #
    lttri2d
    @46
    @66
    @63
    @46
    @64
    @63
    @65
    @46
    @64
    wa
    #
    @18
    @6
    @35
    c.x
    co
    #
    @35
    @70
    @17
    @35
    @6
    c.x
    @70
    @26
    @56
    cG
    cD
    cfv
    #
    @16
    clt
    wbr
    @17
    @35
    wceq
    wph
    @26
    @45
    @64
    coe1mul3.g1
    ad2antrr
    @46
    @56
    @64
    @45
    @56
    wph
    @58
    adantl
    adantr
    @70
    @72
    cJ
    @16
    wph
    @72
    cxr
    wcel
    #
    @45
    @64
    wph
    @26
    @73
    coe1mul3.g1
    cB
    cD
    cY
    cR
    cG
    coe1mul3.d
    coe1mul3.s
    coe1mul3.b
    deg1xrcl
    syl
    ad2antrr
    wph
    cJ
    cxr
    wcel
    @45
    @64
    wph
    cJ
    wph
    cJ
    coe1mul3.g2
    nn0red
    #
    rexrd
    ad2antrr
    @46
    @16
    cxr
    wcel
    @64
    @46
    @16
    @46
    @0
    @4
    wph
    @0
    cr
    wcel
    @45
    wph
    @0
    @28
    nn0red
    adantr
    #
    @68
    resubcld
    rexrd
    adantr
    wph
    @72
    cJ
    cle
    wbr
    @45
    @64
    coe1mul3.g3
    ad2antrr
    @46
    @64
    cJ
    @16
    clt
    wbr
    #
    @46
    @64
    @4
    cJ
    caddc
    co
    @0
    clt
    wbr
    @76
    @46
    @4
    cI
    cJ
    @68
    @69
    wph
    cJ
    cr
    wcel
    @45
    @74
    adantr
    #
    ltadd1d
    @46
    @4
    cJ
    @0
    @68
    @77
    @75
    ltaddsub2d
    bitrd
    biimpa
    xrlelttrd
    @8
    cB
    cD
    cY
    cR
    cG
    @16
    @35
    coe1mul3.d
    coe1mul3.s
    coe1mul3.b
    @37
    @57
    deg1lt
    syl3anc
    oveq2d
    @46
    @71
    @35
    wceq
    #
    @64
    @46
    @24
    @47
    @78
    @49
    @54
    @34
    cR
    c.x
    @6
    @35
    @36
    coe1mul3.u
    @37
    ringrz
    syl2anc
    adantr
    eqtrd
    @46
    @65
    wa
    #
    @18
    @35
    @17
    c.x
    co
    #
    @35
    @79
    @6
    @35
    @17
    c.x
    @79
    @25
    @51
    cF
    cD
    cfv
    #
    @4
    clt
    wbr
    @6
    @35
    wceq
    wph
    @25
    @45
    @65
    coe1mul3.f1
    ad2antrr
    @46
    @51
    @65
    @67
    adantr
    @79
    @81
    cI
    @4
    wph
    @81
    cxr
    wcel
    #
    @45
    @65
    wph
    @25
    @82
    coe1mul3.f1
    cB
    cD
    cY
    cR
    cF
    coe1mul3.d
    coe1mul3.s
    coe1mul3.b
    deg1xrcl
    syl
    ad2antrr
    wph
    cI
    cxr
    wcel
    @45
    @65
    wph
    cI
    @43
    rexrd
    ad2antrr
    @46
    @4
    cxr
    wcel
    @65
    @46
    @4
    @68
    rexrd
    adantr
    wph
    @81
    cI
    cle
    wbr
    @45
    @65
    coe1mul3.f3
    ad2antrr
    @46
    @65
    simpr
    xrlelttrd
    @5
    cB
    cD
    cY
    cR
    cF
    @4
    @35
    coe1mul3.d
    coe1mul3.s
    coe1mul3.b
    @37
    @52
    deg1lt
    syl3anc
    oveq1d
    @46
    @80
    @35
    wceq
    #
    @65
    @46
    @24
    @48
    @83
    @49
    @59
    @34
    cR
    c.x
    @17
    @35
    @36
    coe1mul3.u
    @37
    ringlz
    syl2anc
    adantr
    eqtrd
    jaodan
    ex
    sylbid
    impr
    sylan2b
    @38
    suppss2
    gsumpt
    wph
    @39
    @30
    @33
    wceq
    @44
    vy
    cI
    @18
    @33
    @15
    @19
    @4
    cI
    wceq
    #
    @6
    @21
    @17
    @32
    c.x
    @4
    cI
    @5
    fveq2
    @84
    @16
    @31
    @8
    @4
    cI
    @0
    cmin
    oveq2
    fveq2d
    oveq12d
    @60
    @21
    @32
    c.x
    ovex
    fvmpt
    syl
    wph
    @32
    @22
    @21
    c.x
    wph
    @31
    cJ
    @8
    wph
    cI
    cJ
    wph
    cI
    coe1mul3.f2
    nn0cnd
    wph
    cJ
    coe1mul3.g2
    nn0cnd
    pncan2d
    fveq2d
    oveq2d
    3eqtrd
    3eqtrd
end
