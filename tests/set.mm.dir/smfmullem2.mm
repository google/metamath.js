include "cs4.mm"
include "wcel.mm"
include "cc0.mm"
include "cfv.mm"
include "c1.mm"
include "cioo.mm"
include "co.mm"
include "c2.mm"
include "c3.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "cq.mm"
include "cfz.mm"
include "cmap.mm"
include "cmul.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "c4.mm"
include "cfzo.mm"
include "cword.mm"
include "chash.mm"
include "wceq.mm"
include "s4cld.mm"
include "s4len.mm"
include "a1i.mm"
include "jca.mm"
include "cvv.mm"
include "cn0.mm"
include "wb.mm"
include "qex.mm"
include "4nn0.mm"
include "wrdmap.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "caddc.mm"
include "cz.mm"
include "3z.mm"
include "fzval3.mm"
include "ax-mp.mm"
include "3p1e4.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "eqcomi.mm"
include "oveq2d.mm"
include "eleqtrd.mm"
include "simpr.mm"
include "s4fv0.mm"
include "syl.mm"
include "s4fv1.mm"
include "oveq12d.mm"
include "adantr.mm"
include "s4fv2.mm"
include "s4fv3.mm"
include "syldan.mm"
include "adantlr.mm"
include "cr.mm"
include "ad2antrr.mm"
include "cmin.mm"
include "simplr.mm"
include "smfmullem1.mm"
include "ralrimiva.mm"
include "fveq1.mm"
include "raleqdv.mm"
include "ralbidv.mm"
include "bitrd.mm"
include "elrab2.mm"
include "sylibr.mm"
include "qssre.mm"
include "sseldi.mm"
include "rexrd.mm"
include "cxr.mm"
include "cle.mm"
include "cif.mm"
include "crp.mm"
include "1rp.mm"
include "cabs.mm"
include "cdiv.mm"
include "remulcld.mm"
include "difrp.mm"
include "1red.mm"
include "recnd.mm"
include "abscld.mm"
include "readdcld.mm"
include "0re.mm"
include "rpgt0d.mm"
include "absge0d.mm"
include "addge01d.mm"
include "letrd.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "rpdivcld.mm"
include "eqeltrd.mm"
include "ifcld.mm"
include "rpred.mm"
include "resubcld.mm"
include "iooltub.mm"
include "syl3anc.mm"
include "ioogtlb.mm"
include "eliood.mm"
include "eqcomd.mm"
include "nfv.mm"
include "nfcv.mm"
include "crab.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "rspcef.mm"

theorem smfmullem2
  let wph: wff ph
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cP: class P
  let cR: class R
  let cS: class S
  let cU: class U
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vq: setvar q
  let vk: setvar k
  let vx: setvar x
  assume smfmullem2.a: |- ( ph -> A e. RR )
  assume smfmullem2.k: |- K = { q e. ( QQ ^m ( 0 ... 3 ) ) | A. u e. ( ( q ` 0 ) (,) ( q ` 1 ) ) A. v e. ( ( q ` 2 ) (,) ( q ` 3 ) ) ( u x. v ) < A }
  assume smfmullem2.u: |- ( ph -> U e. RR )
  assume smfmullem2.v: |- ( ph -> V e. RR )
  assume smfmullem2.l: |- ( ph -> ( U x. V ) < A )
  assume smfmullem2.p: |- ( ph -> P e. QQ )
  assume smfmullem2.r: |- ( ph -> R e. QQ )
  assume smfmullem2.s: |- ( ph -> S e. QQ )
  assume smfmullem2.z: |- ( ph -> Z e. QQ )
  assume smfmullem2.p2: |- ( ph -> P e. ( ( U - Y ) (,) U ) )
  assume smfmullem2.42: |- ( ph -> R e. ( U (,) ( U + Y ) ) )
  assume smfmullem2.w2: |- ( ph -> S e. ( ( V - Y ) (,) V ) )
  assume smfmullem2.z2: |- ( ph -> Z e. ( V (,) ( V + Y ) ) )
  assume smfmullem2.x: |- X = ( ( A - ( U x. V ) ) / ( 1 + ( ( abs ` U ) + ( abs ` V ) ) ) )
  assume smfmullem2.y: |- Y = if ( 1 <_ X , 1 , X )

  disjoint A q
  disjoint P q
  disjoint P u
  disjoint P v
  disjoint q u
  disjoint q v
  disjoint u v
  disjoint R q
  disjoint R u
  disjoint R v
  disjoint S q
  disjoint S u
  disjoint S v
  disjoint U q
  disjoint V q
  disjoint Z q
  disjoint Z u
  disjoint Z v
  disjoint ph u
  disjoint ph v
  disjoint k x
  assert |- ( ph -> E. q e. K ( U e. ( ( q ` 0 ) (,) ( q ` 1 ) ) /\ V e. ( ( q ` 2 ) (,) ( q ` 3 ) ) ) )

  proof
    wph
    cP
    cR
    cS
    cZ
    cs4
    #
    cK
    wcel
    #
    cU
    cc0
    @0
    cfv
    #
    c1
    @0
    cfv
    #
    cioo
    co
    #
    wcel
    #
    cV
    c2
    @0
    cfv
    #
    c3
    @0
    cfv
    #
    cioo
    co
    #
    wcel
    #
    wa
    #
    cU
    cc0
    vq
    cv
    #
    cfv
    #
    c1
    @11
    cfv
    #
    cioo
    co
    #
    wcel
    #
    cV
    c2
    @11
    cfv
    #
    c3
    @11
    cfv
    #
    cioo
    co
    #
    wcel
    #
    wa
    #
    vq
    cK
    wrex
    wph
    @0
    cq
    cc0
    c3
    cfz
    co
    #
    cmap
    co
    #
    wcel
    #
    vu
    cv
    #
    vv
    cv
    #
    cmul
    co
    cA
    clt
    wbr
    #
    vv
    @8
    wral
    #
    vu
    @4
    wral
    #
    wa
    @1
    wph
    @23
    @28
    wph
    @0
    cq
    cc0
    c4
    cfzo
    co
    #
    cmap
    co
    #
    @22
    wph
    @0
    cq
    cword
    wcel
    #
    @0
    chash
    cfv
    c4
    wceq
    #
    wa
    #
    @0
    @30
    wcel
    #
    wph
    @31
    @32
    wph
    cP
    cR
    cS
    cZ
    cq
    smfmullem2.p
    smfmullem2.r
    smfmullem2.s
    smfmullem2.z
    s4cld
    @32
    wph
    cP
    cR
    cS
    cZ
    s4len
    a1i
    jca
    wph
    cq
    cvv
    wcel
    #
    c4
    cn0
    wcel
    #
    @33
    @34
    wb
    @35
    wph
    qex
    a1i
    @36
    wph
    4nn0
    a1i
    c4
    cq
    @0
    cvv
    wrdmap
    syl2anc
    mpbid
    wph
    @29
    @21
    cq
    cmap
    @29
    @21
    wceq
    wph
    @21
    @29
    @21
    cc0
    c3
    c1
    caddc
    co
    #
    cfzo
    co
    #
    @29
    c3
    cz
    wcel
    @21
    @38
    wceq
    3z
    cc0
    c3
    fzval3
    ax-mp
    @37
    c4
    cc0
    cfzo
    3p1e4
    oveq2i
    eqtri
    eqcomi
    a1i
    oveq2d
    eleqtrd
    wph
    @27
    vu
    @4
    wph
    @24
    @4
    wcel
    #
    @24
    cP
    cR
    cioo
    co
    #
    wcel
    #
    @27
    wph
    @39
    wa
    @24
    @4
    @40
    wph
    @39
    simpr
    wph
    @4
    @40
    wceq
    @39
    wph
    @2
    cP
    @3
    cR
    cioo
    wph
    cP
    cq
    wcel
    @2
    cP
    wceq
    smfmullem2.p
    cP
    cR
    cS
    cZ
    cq
    s4fv0
    syl
    wph
    cR
    cq
    wcel
    @3
    cR
    wceq
    smfmullem2.r
    cP
    cR
    cS
    cZ
    cq
    s4fv1
    syl
    oveq12d
    #
    adantr
    eleqtrd
    wph
    @41
    wa
    #
    @26
    vv
    @8
    @43
    @25
    @8
    wcel
    #
    @25
    cS
    cZ
    cioo
    co
    #
    wcel
    #
    @26
    wph
    @44
    @46
    @41
    wph
    @44
    @46
    @46
    wph
    @44
    wa
    @25
    @8
    @45
    wph
    @44
    simpr
    wph
    @8
    @45
    wceq
    @44
    wph
    @6
    cS
    @7
    cZ
    cioo
    wph
    cS
    cq
    wcel
    @6
    cS
    wceq
    smfmullem2.s
    cP
    cR
    cS
    cZ
    cq
    s4fv2
    syl
    wph
    cZ
    cq
    wcel
    @7
    cZ
    wceq
    smfmullem2.z
    cP
    cR
    cS
    cZ
    cq
    s4fv3
    syl
    oveq12d
    #
    adantr
    eleqtrd
    wph
    @46
    simpr
    syldan
    adantlr
    @43
    @46
    wa
    cA
    cP
    cR
    cS
    cU
    @24
    @25
    cV
    cX
    cY
    cZ
    wph
    cA
    cr
    wcel
    #
    @41
    @46
    smfmullem2.a
    ad2antrr
    wph
    cU
    cr
    wcel
    @41
    @46
    smfmullem2.u
    ad2antrr
    wph
    cV
    cr
    wcel
    @41
    @46
    smfmullem2.v
    ad2antrr
    wph
    cU
    cV
    cmul
    co
    #
    cA
    clt
    wbr
    #
    @41
    @46
    smfmullem2.l
    ad2antrr
    smfmullem2.x
    smfmullem2.y
    wph
    cP
    cU
    cY
    cmin
    co
    #
    cU
    cioo
    co
    wcel
    #
    @41
    @46
    smfmullem2.p2
    ad2antrr
    wph
    cR
    cU
    cU
    cY
    caddc
    co
    #
    cioo
    co
    wcel
    #
    @41
    @46
    smfmullem2.42
    ad2antrr
    wph
    cS
    cV
    cY
    cmin
    co
    #
    cV
    cioo
    co
    wcel
    #
    @41
    @46
    smfmullem2.w2
    ad2antrr
    wph
    cZ
    cV
    cV
    cY
    caddc
    co
    #
    cioo
    co
    wcel
    #
    @41
    @46
    smfmullem2.z2
    ad2antrr
    wph
    @41
    @46
    simplr
    @43
    @46
    simpr
    smfmullem1
    syldan
    ralrimiva
    syldan
    ralrimiva
    jca
    @26
    vv
    @18
    wral
    #
    vu
    @14
    wral
    #
    @28
    vq
    @0
    @22
    cK
    @11
    @0
    wceq
    #
    @60
    @59
    vu
    @4
    wral
    @28
    @61
    @59
    vu
    @14
    @4
    @61
    @12
    @2
    @13
    @3
    cioo
    cc0
    @11
    @0
    fveq1
    c1
    @11
    @0
    fveq1
    oveq12d
    #
    raleqdv
    @61
    @59
    @27
    vu
    @4
    @61
    @26
    vv
    @18
    @8
    @61
    @16
    @6
    @17
    @7
    cioo
    c2
    @11
    @0
    fveq1
    c3
    @11
    @0
    fveq1
    oveq12d
    #
    raleqdv
    ralbidv
    bitrd
    smfmullem2.k
    elrab2
    sylibr
    wph
    @5
    @9
    wph
    cU
    @40
    @4
    wph
    cP
    cR
    cU
    wph
    cP
    wph
    cq
    cr
    cP
    qssre
    smfmullem2.p
    sseldi
    rexrd
    wph
    cR
    wph
    cq
    cr
    cR
    qssre
    smfmullem2.r
    sseldi
    rexrd
    smfmullem2.u
    wph
    @51
    cxr
    wcel
    cU
    cxr
    wcel
    #
    @52
    cP
    cU
    clt
    wbr
    wph
    @51
    wph
    cU
    cY
    smfmullem2.u
    wph
    cY
    wph
    cY
    c1
    cX
    cle
    wbr
    #
    c1
    cX
    cif
    #
    crp
    cY
    @66
    wceq
    wph
    smfmullem2.y
    a1i
    wph
    @65
    c1
    cX
    crp
    c1
    crp
    wcel
    wph
    1rp
    a1i
    #
    wph
    cX
    cA
    @49
    cmin
    co
    #
    c1
    cU
    cabs
    cfv
    #
    cV
    cabs
    cfv
    #
    caddc
    co
    #
    caddc
    co
    #
    cdiv
    co
    #
    crp
    cX
    @73
    wceq
    wph
    smfmullem2.x
    a1i
    wph
    @68
    @72
    wph
    @50
    @68
    crp
    wcel
    #
    smfmullem2.l
    wph
    @49
    cr
    wcel
    @48
    @50
    @74
    wb
    wph
    cU
    cV
    smfmullem2.u
    smfmullem2.v
    remulcld
    smfmullem2.a
    @49
    cA
    difrp
    syl2anc
    mpbid
    wph
    @72
    wph
    c1
    @71
    wph
    1red
    #
    wph
    @69
    @70
    wph
    cU
    wph
    cU
    smfmullem2.u
    recnd
    #
    abscld
    #
    wph
    cV
    wph
    cV
    smfmullem2.v
    recnd
    #
    abscld
    #
    readdcld
    #
    readdcld
    #
    wph
    cc0
    c1
    @72
    cc0
    cr
    wcel
    wph
    0re
    a1i
    #
    @75
    @81
    wph
    c1
    @67
    rpgt0d
    wph
    cc0
    @71
    cle
    wbr
    c1
    @72
    cle
    wbr
    wph
    cc0
    @69
    @71
    @82
    @77
    @80
    wph
    cU
    @76
    absge0d
    wph
    cc0
    @70
    cle
    wbr
    @69
    @71
    cle
    wbr
    wph
    cV
    @78
    absge0d
    wph
    @69
    @70
    @77
    @79
    addge01d
    mpbid
    letrd
    wph
    c1
    @71
    @75
    @80
    addge01d
    mpbid
    ltletrd
    elrpd
    rpdivcld
    eqeltrd
    ifcld
    eqeltrd
    rpred
    #
    resubcld
    rexrd
    wph
    cU
    smfmullem2.u
    rexrd
    #
    smfmullem2.p2
    @51
    cU
    cP
    iooltub
    syl3anc
    wph
    @64
    @53
    cxr
    wcel
    @54
    cU
    cR
    clt
    wbr
    @84
    wph
    @53
    wph
    cU
    cY
    smfmullem2.u
    @83
    readdcld
    rexrd
    smfmullem2.42
    cU
    @53
    cR
    ioogtlb
    syl3anc
    eliood
    wph
    @4
    @40
    @42
    eqcomd
    eleqtrd
    wph
    cV
    @45
    @8
    wph
    cS
    cZ
    cV
    wph
    cS
    wph
    cq
    cr
    cS
    qssre
    smfmullem2.s
    sseldi
    rexrd
    wph
    cZ
    wph
    cq
    cr
    cZ
    qssre
    smfmullem2.z
    sseldi
    rexrd
    smfmullem2.v
    wph
    @55
    cxr
    wcel
    cV
    cxr
    wcel
    #
    @56
    cS
    cV
    clt
    wbr
    wph
    @55
    wph
    cV
    cY
    smfmullem2.v
    @83
    resubcld
    rexrd
    wph
    cV
    smfmullem2.v
    rexrd
    #
    smfmullem2.w2
    @55
    cV
    cS
    iooltub
    syl3anc
    wph
    @85
    @57
    cxr
    wcel
    @58
    cV
    cZ
    clt
    wbr
    @86
    wph
    @57
    wph
    cV
    cY
    smfmullem2.v
    @83
    readdcld
    rexrd
    smfmullem2.z2
    cV
    @57
    cZ
    ioogtlb
    syl3anc
    eliood
    wph
    @8
    @45
    @47
    eqcomd
    eleqtrd
    jca
    @20
    @10
    vq
    @0
    cK
    @10
    vq
    nfv
    vq
    @0
    nfcv
    vq
    cK
    @60
    vq
    @22
    crab
    smfmullem2.k
    @60
    vq
    @22
    nfrab1
    nfcxfr
    @61
    @15
    @5
    @19
    @9
    @61
    @14
    @4
    cU
    @62
    eleq2d
    @61
    @18
    @8
    cV
    @63
    eleq2d
    anbi12d
    rspcef
    syl2anc
end
