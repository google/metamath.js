include "csn.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "cdif.mm"
include "wrex.mm"
include "wa.mm"
include "c0g.mm"
include "cur.mm"
include "wcel.mm"
include "wne.mm"
include "clmod.mm"
include "crg.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "lmodring.mm"
include "eqid.mm"
include "ringidcl.mm"
include "3syl.mm"
include "cdr.mm"
include "lvecdrng.mm"
include "drngunz.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "ad2antrr.mm"
include "lmod0vcl.mm"
include "lmodvs1.mm"
include "syl2anc.mm"
include "oveq2.mm"
include "adantl.mm"
include "adantr.mm"
include "simpr.mm"
include "lspsneq0b.mm"
include "biimpar.mm"
include "3eqtr4rd.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "wss.mm"
include "eqimss.mm"
include "clss.mm"
include "lspsncl.mm"
include "lspsnel5.mm"
include "mpbird.mm"
include "wb.mm"
include "lspsnel.mm"
include "mpbid.mm"
include "simprl.mm"
include "biimpd.mm"
include "necon3d.mm"
include "imp.mm"
include "eqnetrrd.mm"
include "lvecvsn0.mm"
include "simpld.mm"
include "jca.mm"
include "ex.mm"
include "reximdv2.mm"
include "mpd.mm"
include "pm2.61dane.mm"
include "wi.mm"
include "eldifi.mm"
include "eldifsni.mm"
include "lspsnvs.mm"
include "syl121anc.mm"
include "sneq.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "biimprcd.mm"
include "syl6.mm"
include "rexlimdv.mm"
include "impbid.mm"
include "weq.mm"
include "cbvrexv.mm"
include "syl6bb.mm"

theorem lspsneq
  let wph: wff ph
  let cS: class S
  let c.x: class .x.
  let vk: setvar k
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vj: setvar j
  assume lspsneq.v: |- V = ( Base ` W )
  assume lspsneq.s: |- S = ( Scalar ` W )
  assume lspsneq.k: |- K = ( Base ` S )
  assume lspsneq.o: |- .0. = ( 0g ` S )
  assume lspsneq.t: |- .x. = ( .s ` W )
  assume lspsneq.n: |- N = ( LSpan ` W )
  assume lspsneq.w: |- ( ph -> W e. LVec )
  assume lspsneq.x: |- ( ph -> X e. V )
  assume lspsneq.y: |- ( ph -> Y e. V )

  disjoint K k
  disjoint .0. k
  disjoint .x. k
  disjoint X k
  disjoint Y k
  disjoint j k
  disjoint K j
  disjoint N j
  disjoint .0. j
  disjoint S j
  disjoint .x. j
  disjoint V j
  disjoint W j
  disjoint X j
  disjoint Y j
  disjoint j ph
  assert |- ( ph -> ( ( N ` { X } ) = ( N ` { Y } ) <-> E. k e. ( K \ { .0. } ) X = ( k .x. Y ) ) )

  proof
    wph
    cX
    csn
    #
    cN
    cfv
    #
    cY
    csn
    cN
    cfv
    #
    wceq
    #
    cX
    vj
    cv
    #
    cY
    c.x
    co
    #
    wceq
    #
    vj
    cK
    c.0
    csn
    #
    cdif
    #
    wrex
    #
    cX
    vk
    cv
    #
    cY
    c.x
    co
    #
    wceq
    #
    vk
    @8
    wrex
    wph
    @3
    @9
    wph
    @3
    @9
    wph
    @3
    wa
    #
    @9
    cY
    cW
    c0g
    cfv
    #
    @13
    cY
    @14
    wceq
    #
    wa
    #
    cS
    cur
    cfv
    #
    @8
    wcel
    #
    cX
    @17
    cY
    c.x
    co
    #
    wceq
    #
    @9
    wph
    @18
    @3
    @15
    wph
    @17
    cK
    wcel
    #
    @17
    c.0
    wne
    #
    @18
    wph
    cW
    clmod
    wcel
    #
    cS
    crg
    wcel
    @21
    wph
    cW
    clvec
    wcel
    #
    @23
    lspsneq.w
    cW
    lveclmod
    #
    syl
    #
    cS
    cW
    lspsneq.s
    lmodring
    cK
    cS
    @17
    lspsneq.k
    @17
    eqid
    #
    ringidcl
    3syl
    wph
    @24
    cS
    cdr
    wcel
    @22
    lspsneq.w
    cS
    cW
    lspsneq.s
    lvecdrng
    cS
    @17
    c.0
    lspsneq.o
    @27
    drngunz
    3syl
    @17
    cK
    c.0
    eldifsn
    sylanbrc
    ad2antrr
    @16
    @17
    @14
    c.x
    co
    #
    @14
    @19
    cX
    wph
    @28
    @14
    wceq
    #
    @3
    @15
    wph
    @23
    @14
    cV
    wcel
    #
    @29
    @26
    wph
    @24
    @23
    @30
    lspsneq.w
    @25
    cV
    cW
    @14
    lspsneq.v
    @14
    eqid
    #
    lmod0vcl
    3syl
    c.x
    @17
    cS
    cV
    cW
    @14
    lspsneq.v
    lspsneq.s
    lspsneq.t
    @27
    lmodvs1
    syl2anc
    ad2antrr
    @15
    @19
    @28
    wceq
    @13
    cY
    @14
    @17
    c.x
    oveq2
    adantl
    @13
    cX
    @14
    wceq
    #
    @15
    @13
    cN
    cV
    cW
    cX
    cY
    @14
    lspsneq.v
    @31
    lspsneq.n
    wph
    @23
    @3
    @26
    adantr
    #
    wph
    cX
    cV
    wcel
    @3
    lspsneq.x
    adantr
    #
    wph
    cY
    cV
    wcel
    #
    @3
    lspsneq.y
    adantr
    #
    wph
    @3
    simpr
    lspsneq0b
    #
    biimpar
    3eqtr4rd
    @6
    @20
    vj
    @17
    @8
    @4
    @17
    wceq
    @5
    @19
    cX
    @4
    @17
    cY
    c.x
    oveq1
    eqeq2d
    rspcev
    syl2anc
    @13
    cY
    @14
    wne
    #
    wa
    #
    @6
    vj
    cK
    wrex
    #
    @9
    @13
    @40
    @38
    @13
    cX
    @2
    wcel
    #
    @40
    @13
    @41
    @1
    @2
    wss
    #
    @3
    @42
    wph
    @1
    @2
    eqimss
    adantl
    @13
    cW
    clss
    cfv
    #
    @2
    cN
    cV
    cW
    cX
    lspsneq.v
    @43
    eqid
    #
    lspsneq.n
    @33
    wph
    @2
    @43
    wcel
    #
    @3
    wph
    @23
    @35
    @45
    @26
    lspsneq.y
    @43
    cN
    cV
    cW
    cY
    lspsneq.v
    @44
    lspsneq.n
    lspsncl
    syl2anc
    adantr
    @34
    lspsnel5
    mpbird
    @13
    @23
    @35
    @41
    @40
    wb
    @33
    @36
    c.x
    cX
    vj
    cS
    cK
    cN
    cV
    cW
    cY
    lspsneq.s
    lspsneq.k
    lspsneq.v
    lspsneq.t
    lspsneq.n
    lspsnel
    syl2anc
    mpbid
    adantr
    @39
    @6
    @6
    vj
    cK
    @8
    @39
    @4
    cK
    wcel
    #
    @6
    wa
    #
    @4
    @8
    wcel
    #
    @6
    wa
    @39
    @47
    wa
    #
    @48
    @6
    @49
    @46
    @4
    c.0
    wne
    #
    @48
    @39
    @46
    @6
    simprl
    #
    @49
    @50
    @38
    @49
    @5
    @14
    wne
    @50
    @38
    wa
    @49
    cX
    @5
    @14
    @47
    @6
    @39
    @46
    @6
    simpr
    adantl
    #
    @39
    cX
    @14
    wne
    #
    @47
    @13
    @38
    @53
    @13
    cX
    @14
    cY
    @14
    @13
    @32
    @15
    @37
    biimpd
    necon3d
    imp
    adantr
    eqnetrrd
    @49
    @4
    c.x
    cS
    cK
    c.0
    cV
    cW
    cY
    @14
    lspsneq.v
    lspsneq.t
    lspsneq.s
    lspsneq.k
    lspsneq.o
    @31
    @13
    @24
    @38
    @47
    wph
    @24
    @3
    lspsneq.w
    adantr
    ad2antrr
    @51
    @13
    @35
    @38
    @47
    @36
    ad2antrr
    lvecvsn0
    mpbid
    simpld
    @4
    cK
    c.0
    eldifsn
    sylanbrc
    @52
    jca
    ex
    reximdv2
    mpd
    pm2.61dane
    ex
    wph
    @6
    @3
    vj
    @8
    wph
    @48
    @5
    csn
    #
    cN
    cfv
    #
    @2
    wceq
    #
    @6
    @3
    wi
    wph
    @48
    @56
    wph
    @48
    wa
    @24
    @46
    @50
    @35
    @56
    wph
    @24
    @48
    lspsneq.w
    adantr
    @48
    @46
    wph
    @4
    cK
    @7
    eldifi
    adantl
    @48
    @50
    wph
    @4
    cK
    c.0
    eldifsni
    adantl
    wph
    @35
    @48
    lspsneq.y
    adantr
    @4
    c.x
    cS
    cK
    cN
    cV
    cW
    cY
    c.0
    lspsneq.v
    lspsneq.s
    lspsneq.t
    lspsneq.k
    lspsneq.o
    lspsneq.n
    lspsnvs
    syl121anc
    ex
    @6
    @3
    @56
    @6
    @1
    @55
    @2
    @6
    @0
    @54
    cN
    cX
    @5
    sneq
    fveq2d
    eqeq1d
    biimprcd
    syl6
    rexlimdv
    impbid
    @6
    @12
    vj
    vk
    @8
    vj
    vk
    weq
    @5
    @11
    cX
    @4
    @10
    cY
    c.x
    oveq1
    eqeq2d
    cbvrexv
    syl6bb
end
