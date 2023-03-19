include "cv.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cin.mm"
include "crab.mm"
include "wcel.mm"
include "cq.mm"
include "cfv.mm"
include "wa.mm"
include "ciun.mm"
include "wb.mm"
include "wal.mm"
include "wceq.mm"
include "wrex.mm"
include "cmin.mm"
include "cioo.mm"
include "cr.mm"
include "simpl.mm"
include "inss1.mm"
include "rabid.mm"
include "simplbi.mm"
include "sseldi.mm"
include "adantl.mm"
include "syl2anc.mm"
include "rexrd.mm"
include "adantr.mm"
include "elinel2.mm"
include "syldan.mm"
include "sylan2.mm"
include "resubcld.mm"
include "simprbi.mm"
include "ltaddsubd.mm"
include "mpbid.mm"
include "qelioo.mm"
include "cxr.mm"
include "ad2antrr.mm"
include "qre.mm"
include "elioore.mm"
include "simpr.mm"
include "iooltub.mm"
include "syl3anc.mm"
include "ltsub13d.mm"
include "adantlr.mm"
include "nfv.mm"
include "nfre1.mm"
include "wi.mm"
include "simplr.mm"
include "w3a.mm"
include "3ad2ant3.mm"
include "3adant3.mm"
include "3ad2ant2.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "ltadd2dd.mm"
include "recnd.mm"
include "pncan3d.mm"
include "breqtrd.mm"
include "ad5ant135.mm"
include "jca.mm"
include "sylibr.mm"
include "cvv.mm"
include "id.mm"
include "qex.mm"
include "rabex.mm"
include "a1i.mm"
include "fvmpt2.mm"
include "ad4antlr.mm"
include "eleqtrrd.mm"
include "simp-5r.mm"
include "syl.mm"
include "ioogtlb.mm"
include "ad5ant13.mm"
include "ad4ant14.mm"
include "jca32.mm"
include "rspe.mm"
include "ex.mm"
include "rexlimd.mm"
include "mpd.mm"
include "eliun.mm"
include "reximdva.mm"
include "rexbii.mm"
include "bitri.mm"
include "biimpi.mm"
include "simpld.mm"
include "elinel1.mm"
include "3adant2.mm"
include "readdcld.mm"
include "simp2l.mm"
include "ssrab2.mm"
include "eleqtrd.mm"
include "ssriv.mm"
include "sseli.mm"
include "simprld.mm"
include "simprrd.mm"
include "ltadd12dd.mm"
include "rabidim2.mm"
include "lttrd.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "impbid.mm"
include "alrimi.mm"
include "nfrab1.mm"
include "nfcv.mm"
include "nfiun.mm"
include "dfcleqf.mm"

theorem smfaddlem1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cK: class K
  let vq: setvar q
  let vp: setvar p
  let vk: setvar k
  assume smfaddlem1.x: |- F/ x ph
  assume smfaddlem1.b: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume smfaddlem1.d: |- ( ( ph /\ x e. C ) -> D e. RR )
  assume smfaddlem1.r: |- ( ph -> R e. RR )
  assume smfaddlem1.k: |- K = ( p e. QQ |-> { q e. QQ | ( p + q ) < R } )

  disjoint A p
  disjoint A q
  disjoint p q
  disjoint B p
  disjoint B q
  disjoint C p
  disjoint C q
  disjoint D p
  disjoint D q
  disjoint K x
  disjoint R p
  disjoint R q
  disjoint p ph
  disjoint ph q
  disjoint p x
  disjoint q x
  disjoint k x
  assert |- ( ph -> { x e. ( A i^i C ) | ( B + D ) < R } = U_ p e. QQ U_ q e. ( K ` p ) { x e. ( A i^i C ) | ( B < p /\ D < q ) } )

  proof
    wph
    vx
    cv
    #
    cB
    cD
    caddc
    co
    #
    cR
    clt
    wbr
    #
    vx
    cA
    cC
    cin
    #
    crab
    #
    wcel
    #
    @0
    vp
    cq
    vq
    vp
    cv
    #
    cK
    cfv
    #
    cB
    @6
    clt
    wbr
    #
    cD
    vq
    cv
    #
    clt
    wbr
    #
    wa
    #
    vx
    @3
    crab
    #
    ciun
    #
    ciun
    #
    wcel
    #
    wb
    #
    vx
    wal
    @4
    @14
    wceq
    wph
    @16
    vx
    smfaddlem1.x
    wph
    @5
    @15
    wph
    @5
    @15
    wph
    @5
    wa
    #
    @0
    @13
    wcel
    #
    vp
    cq
    wrex
    #
    @15
    @17
    @6
    cB
    cR
    cD
    cmin
    co
    #
    cioo
    co
    wcel
    #
    vp
    cq
    wrex
    @19
    @17
    vp
    cB
    @20
    @17
    cB
    @17
    wph
    @0
    cA
    wcel
    #
    cB
    cr
    wcel
    #
    wph
    @5
    simpl
    @5
    @22
    wph
    @5
    @3
    cA
    @0
    cA
    cC
    inss1
    @5
    @0
    @3
    wcel
    #
    @2
    @2
    vx
    @3
    rabid
    #
    simplbi
    #
    sseldi
    adantl
    smfaddlem1.b
    syl2anc
    #
    rexrd
    #
    @17
    @20
    @17
    cR
    cD
    wph
    cR
    cr
    wcel
    #
    @5
    smfaddlem1.r
    adantr
    #
    @5
    wph
    @24
    cD
    cr
    wcel
    #
    @26
    wph
    @24
    @0
    cC
    wcel
    #
    @31
    @24
    @32
    wph
    @0
    cA
    cC
    elinel2
    adantl
    smfaddlem1.d
    syldan
    #
    sylan2
    #
    resubcld
    rexrd
    #
    @17
    @2
    cB
    @20
    clt
    wbr
    @5
    @2
    wph
    @5
    @24
    @2
    @25
    simprbi
    adantl
    @17
    cB
    cD
    cR
    @27
    @34
    @30
    ltaddsubd
    mpbid
    qelioo
    @17
    @21
    @18
    vp
    cq
    @17
    @6
    cq
    wcel
    #
    wa
    #
    @21
    @18
    @37
    @21
    wa
    #
    @0
    @12
    wcel
    #
    vq
    @7
    wrex
    #
    @18
    @38
    @9
    cD
    cR
    @6
    cmin
    co
    #
    cioo
    co
    wcel
    #
    vq
    cq
    wrex
    @40
    @38
    vq
    cD
    @41
    @17
    cD
    cxr
    wcel
    #
    @36
    @21
    @17
    cD
    @34
    rexrd
    #
    ad2antrr
    @37
    @41
    cxr
    wcel
    #
    @21
    @37
    @41
    @37
    cR
    @6
    wph
    @29
    @5
    @36
    smfaddlem1.r
    ad2antrr
    @36
    @6
    cr
    wcel
    #
    @17
    @6
    qre
    #
    adantl
    resubcld
    rexrd
    #
    adantr
    @17
    @21
    cD
    @41
    clt
    wbr
    @36
    @17
    @21
    wa
    #
    @6
    cR
    cD
    @21
    @46
    @17
    @6
    cB
    @20
    elioore
    #
    adantl
    @17
    @29
    @21
    @30
    adantr
    #
    @17
    @31
    @21
    @34
    adantr
    @49
    cB
    cxr
    wcel
    #
    @20
    cxr
    wcel
    #
    @21
    @6
    @20
    clt
    wbr
    @17
    @52
    @21
    @28
    adantr
    #
    @17
    @53
    @21
    @35
    adantr
    #
    @17
    @21
    simpr
    #
    cB
    @20
    @6
    iooltub
    syl3anc
    ltsub13d
    adantlr
    qelioo
    @38
    @42
    @40
    vq
    cq
    @38
    vq
    nfv
    @39
    vq
    @7
    nfre1
    @38
    @9
    cq
    wcel
    #
    @42
    @40
    wi
    @38
    @57
    wa
    #
    @42
    @40
    @58
    @42
    wa
    #
    @9
    @7
    wcel
    #
    @39
    @40
    @59
    @9
    @6
    @9
    caddc
    co
    #
    cR
    clt
    wbr
    #
    vq
    cq
    crab
    #
    @7
    @59
    @57
    @62
    wa
    @9
    @63
    wcel
    #
    @59
    @57
    @62
    @38
    @57
    @42
    simplr
    @17
    @21
    @42
    @62
    @36
    @57
    @17
    @21
    @42
    w3a
    #
    @61
    @6
    @41
    caddc
    co
    cR
    clt
    @65
    @9
    @41
    @6
    @42
    @17
    @9
    cr
    wcel
    #
    @21
    @9
    cD
    @41
    elioore
    3ad2ant3
    @65
    cR
    @6
    @17
    @21
    @29
    @42
    @51
    3adant3
    #
    @21
    @17
    @46
    @42
    @50
    3ad2ant2
    #
    resubcld
    #
    @68
    @65
    @43
    @45
    @42
    @9
    @41
    clt
    wbr
    @17
    @21
    @43
    @42
    @44
    3ad2ant1
    @65
    @41
    @69
    rexrd
    @17
    @21
    @42
    simp3
    cD
    @41
    @9
    iooltub
    syl3anc
    ltadd2dd
    @65
    @6
    cR
    @65
    @6
    @68
    recnd
    @65
    cR
    @67
    recnd
    pncan3d
    breqtrd
    ad5ant135
    jca
    @62
    vq
    cq
    rabid
    sylibr
    @36
    @7
    @63
    wceq
    #
    @17
    @21
    @57
    @42
    @36
    @36
    @63
    cvv
    wcel
    #
    @70
    @36
    id
    @71
    @36
    @62
    vq
    cq
    qex
    rabex
    a1i
    vp
    cq
    @63
    cvv
    cK
    smfaddlem1.k
    fvmpt2
    syl2anc
    #
    ad4antlr
    eleqtrrd
    @59
    @24
    @11
    wa
    #
    @39
    @59
    @24
    @8
    @10
    @59
    @5
    @24
    wph
    @5
    @36
    @21
    @57
    @42
    simp-5r
    @26
    syl
    @17
    @21
    @8
    @36
    @57
    @42
    @49
    @52
    @53
    @21
    @8
    @54
    @55
    @56
    cB
    @20
    @6
    ioogtlb
    syl3anc
    ad5ant13
    @37
    @42
    @10
    @21
    @57
    @37
    @42
    wa
    @43
    @45
    @42
    @10
    @17
    @43
    @36
    @42
    @44
    ad2antrr
    @37
    @45
    @42
    @48
    adantr
    @37
    @42
    simpr
    cD
    @41
    @9
    ioogtlb
    syl3anc
    ad4ant14
    jca32
    @11
    vx
    @3
    rabid
    #
    sylibr
    @39
    vq
    @7
    rspe
    syl2anc
    ex
    ex
    rexlimd
    mpd
    vq
    @0
    @7
    @12
    eliun
    #
    sylibr
    ex
    reximdva
    mpd
    vp
    @0
    cq
    @13
    eliun
    #
    sylibr
    ex
    wph
    @15
    @5
    wph
    @15
    wa
    @40
    vp
    cq
    wrex
    #
    @5
    @15
    @77
    wph
    @15
    @77
    @15
    @19
    @77
    @76
    @18
    @40
    vp
    cq
    @75
    rexbii
    bitri
    biimpi
    adantl
    wph
    @77
    @5
    wi
    @15
    wph
    @39
    @5
    vp
    vq
    cq
    @7
    wph
    @36
    @60
    wa
    #
    @39
    @5
    wph
    @78
    @39
    w3a
    #
    @24
    @2
    wa
    @5
    @79
    @24
    @2
    @39
    wph
    @24
    @78
    @39
    @24
    @11
    @39
    @73
    @74
    biimpi
    #
    simpld
    #
    3ad2ant3
    @79
    @1
    @61
    cR
    @79
    cB
    cD
    wph
    @39
    @23
    @78
    @39
    wph
    @24
    @23
    @81
    wph
    @24
    @22
    @23
    @24
    @22
    wph
    @0
    cA
    cC
    elinel1
    adantl
    smfaddlem1.b
    syldan
    sylan2
    3adant2
    #
    wph
    @39
    @31
    @78
    @39
    wph
    @24
    @31
    @81
    @33
    sylan2
    3adant2
    #
    readdcld
    @79
    @6
    @9
    @79
    @36
    @46
    wph
    @36
    @60
    @39
    simp2l
    @47
    syl
    #
    @79
    @57
    @66
    @78
    wph
    @57
    @39
    @78
    @63
    cq
    @9
    @62
    vq
    cq
    ssrab2
    @78
    @9
    @7
    @63
    @36
    @60
    simpr
    @36
    @70
    @60
    @72
    adantr
    eleqtrd
    #
    sseldi
    3ad2ant2
    cq
    cr
    @9
    vp
    cq
    cr
    @47
    ssriv
    sseli
    syl
    #
    readdcld
    wph
    @78
    @29
    @39
    smfaddlem1.r
    3ad2ant1
    @79
    cB
    cD
    @6
    @9
    @82
    @83
    @84
    @86
    @39
    wph
    @8
    @78
    @39
    @24
    @8
    @10
    @80
    simprld
    3ad2ant3
    @39
    wph
    @10
    @78
    @39
    @24
    @8
    @10
    @80
    simprrd
    3ad2ant3
    ltadd12dd
    @78
    wph
    @62
    @39
    @78
    @64
    @62
    @85
    @62
    vq
    cq
    rabidim2
    syl
    3ad2ant2
    lttrd
    jca
    @25
    sylibr
    3exp
    rexlimdvv
    adantr
    mpd
    ex
    impbid
    alrimi
    vx
    @4
    @14
    @2
    vx
    @3
    nfrab1
    vp
    vx
    cq
    @13
    vx
    cq
    nfcv
    vq
    vx
    @7
    @12
    vx
    @7
    nfcv
    @11
    vx
    @3
    nfrab1
    nfiun
    nfiun
    dfcleqf
    sylibr
end
