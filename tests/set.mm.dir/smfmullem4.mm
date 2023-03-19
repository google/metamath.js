include "cmul.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cin.mm"
include "crab.mm"
include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "crest.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "wss.mm"
include "w3a.mm"
include "wrex.mm"
include "cc0.mm"
include "c1.mm"
include "cioo.mm"
include "c2.mm"
include "c3.mm"
include "wa.mm"
include "cmin.mm"
include "cabs.mm"
include "caddc.mm"
include "cdiv.mm"
include "cle.mm"
include "cif.mm"
include "cr.mm"
include "3ad2ant1.mm"
include "inss1.mm"
include "a1i.mm"
include "sselda.mm"
include "syldan.mm"
include "3adant3.mm"
include "elinel2.mm"
include "adantl.mm"
include "simp3.mm"
include "eqid.mm"
include "smfmullem3.mm"
include "rabid.mm"
include "bicomi.mm"
include "biimpi.mm"
include "adantll.mm"
include "adantlr.mm"
include "wceq.mm"
include "cvv.mm"
include "cmpt.mm"
include "inrab.mm"
include "csalg.mm"
include "ssexd.mm"
include "subsalsal.mm"
include "adantr.mm"
include "nfv.mm"
include "nfan.mm"
include "csmblfn.mm"
include "sssmfmpt.mm"
include "cfz.mm"
include "cmap.mm"
include "wf.mm"
include "cq.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "reex.mm"
include "qssre.mm"
include "mapss.mm"
include "mp2an.mm"
include "sstri.mm"
include "id.mm"
include "sseldi.mm"
include "ovexd.mm"
include "elmapd.mm"
include "mpbid.mm"
include "cuz.mm"
include "cz.mm"
include "0z.mm"
include "3z.mm"
include "0re.mm"
include "3re.mm"
include "3pos.mm"
include "ltleii.mm"
include "3pm3.2i.mm"
include "eluz2.mm"
include "mpbir.mm"
include "eluzfz1.mm"
include "ax-mp.mm"
include "ffvelrnd.mm"
include "rexrd.mm"
include "0le1.mm"
include "1re.mm"
include "1lt3.mm"
include "pm3.2i.mm"
include "wb.mm"
include "1z.mm"
include "elfz.mm"
include "mp3an.mm"
include "smfpimioompt.mm"
include "ssdf.mm"
include "0le2.mm"
include "2re.mm"
include "2lt3.mm"
include "2z.mm"
include "eluzfz2.mm"
include "salincld.mm"
include "syl5eqelr.mm"
include "elexd.mm"
include "fvmpt2d.mm"
include "eqcomd.mm"
include "eleqtrd.mm"
include "ex.mm"
include "3adantl3.mm"
include "reximdva.mm"
include "mpd.mm"
include "eliun.mm"
include "sylibr.mm"
include "3exp.mm"
include "ralrimi.mm"
include "nfci.mm"
include "nfrab1.mm"
include "nfmpt.mm"
include "nfcxfr.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfiun.mm"
include "rabssf.mm"
include "syl6eqss.mm"
include "simpr.mm"
include "rabidim2.mm"
include "syl.mm"
include "simprd.mm"
include "simpld.mm"
include "syl6eleq.mm"
include "ad2antlr.mm"
include "oveq1.mm"
include "breq1d.mm"
include "ralbidv.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "oveq2.mm"
include "jca.mm"
include "ssrabf.mm"
include "iunssd.mm"
include "eqssd.mm"
include "com.mm"
include "cdom.mm"
include "ovex.mm"
include "ssdomg.mm"
include "wtru.mm"
include "qct.mm"
include "fzfid.mm"
include "mpct.mm"
include "trud.mm"
include "domtr.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "saliuncl.mm"
include "eqeltrd.mm"

theorem smfmullem4
  let wph: wff ph
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cE: class E
  let cK: class K
  let cV: class V
  let vq: setvar q
  let vk: setvar k
  assume smfmullem4.x: |- F/ x ph
  assume smfmullem4.s: |- ( ph -> S e. SAlg )
  assume smfmullem4.a: |- ( ph -> A e. V )
  assume smfmullem4.b: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume smfmullem4.d: |- ( ( ph /\ x e. C ) -> D e. RR )
  assume smfmullem4.m: |- ( ph -> ( x e. A |-> B ) e. ( SMblFn ` S ) )
  assume smfmullem4.n: |- ( ph -> ( x e. C |-> D ) e. ( SMblFn ` S ) )
  assume smfmullem4.r: |- ( ph -> R e. RR )
  assume smfmullem4.k: |- K = { q e. ( QQ ^m ( 0 ... 3 ) ) | A. u e. ( ( q ` 0 ) (,) ( q ` 1 ) ) A. v e. ( ( q ` 2 ) (,) ( q ` 3 ) ) ( u x. v ) < R }
  assume smfmullem4.e: |- E = ( q e. K |-> { x e. ( A i^i C ) | ( B e. ( ( q ` 0 ) (,) ( q ` 1 ) ) /\ D e. ( ( q ` 2 ) (,) ( q ` 3 ) ) ) } )

  disjoint A q
  disjoint A u
  disjoint A v
  disjoint A x
  disjoint q u
  disjoint q v
  disjoint q x
  disjoint u v
  disjoint u x
  disjoint v x
  disjoint B q
  disjoint B u
  disjoint B v
  disjoint C q
  disjoint C u
  disjoint C v
  disjoint C x
  disjoint D q
  disjoint D u
  disjoint D v
  disjoint K q
  disjoint K x
  disjoint R q
  disjoint R u
  disjoint R v
  disjoint S q
  disjoint ph q
  disjoint ph u
  disjoint ph v
  disjoint k x
  assert |- ( ph -> { x e. ( A i^i C ) | ( B x. D ) < R } e. ( S |`t ( A i^i C ) ) )

  proof
    wph
    cB
    cD
    cmul
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
    vq
    cK
    vq
    cv
    #
    cE
    cfv
    #
    ciun
    #
    cS
    @2
    crest
    co
    #
    wph
    @3
    @6
    wph
    @1
    vx
    cv
    #
    @6
    wcel
    #
    wi
    #
    vx
    @2
    wral
    @3
    @6
    wss
    wph
    @10
    vx
    @2
    smfmullem4.x
    wph
    @8
    @2
    wcel
    #
    @1
    @9
    wph
    @11
    @1
    w3a
    #
    @8
    @5
    wcel
    #
    vq
    cK
    wrex
    #
    @9
    @12
    cB
    cc0
    @4
    cfv
    #
    c1
    @4
    cfv
    #
    cioo
    co
    #
    wcel
    #
    cD
    c2
    @4
    cfv
    #
    c3
    @4
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
    @14
    @12
    vv
    vu
    cR
    cB
    cK
    cD
    cR
    @0
    cmin
    co
    c1
    cB
    cabs
    cfv
    cD
    cabs
    cfv
    caddc
    co
    caddc
    co
    cdiv
    co
    #
    c1
    @24
    cle
    wbr
    c1
    @24
    cif
    #
    vq
    wph
    @11
    cR
    cr
    wcel
    @1
    smfmullem4.r
    3ad2ant1
    smfmullem4.k
    wph
    @11
    cB
    cr
    wcel
    #
    @1
    wph
    @11
    @8
    cA
    wcel
    @26
    wph
    @2
    cA
    @8
    @2
    cA
    wss
    wph
    cA
    cC
    inss1
    a1i
    #
    sselda
    smfmullem4.b
    syldan
    #
    3adant3
    wph
    @11
    cD
    cr
    wcel
    #
    @1
    wph
    @11
    @8
    cC
    wcel
    #
    @29
    @11
    @30
    wph
    @8
    cA
    cC
    elinel2
    adantl
    #
    smfmullem4.d
    syldan
    #
    3adant3
    wph
    @11
    @1
    simp3
    @24
    eqid
    @25
    eqid
    smfmullem3
    @12
    @23
    @13
    vq
    cK
    wph
    @11
    @4
    cK
    wcel
    #
    @23
    @13
    wi
    @1
    wph
    @11
    wa
    #
    @33
    wa
    #
    @23
    @13
    @35
    @23
    wa
    @8
    @23
    vx
    @2
    crab
    #
    @5
    @34
    @23
    @8
    @36
    wcel
    #
    @33
    @11
    @23
    @37
    wph
    @11
    @23
    wa
    #
    @37
    @37
    @38
    @23
    vx
    @2
    rabid
    bicomi
    biimpi
    adantll
    adantlr
    @35
    @36
    @5
    wceq
    #
    @23
    wph
    @33
    @39
    @11
    wph
    @33
    wa
    #
    @5
    @36
    wph
    vq
    cK
    @36
    cE
    cvv
    cE
    vq
    cK
    @36
    cmpt
    #
    wceq
    wph
    smfmullem4.e
    a1i
    @40
    @36
    @7
    @40
    @36
    @18
    vx
    @2
    crab
    #
    @22
    vx
    @2
    crab
    #
    cin
    @7
    @18
    @22
    vx
    @2
    inrab
    @40
    @7
    @42
    @43
    wph
    @7
    csalg
    wcel
    @33
    wph
    @2
    cS
    @7
    cvv
    smfmullem4.s
    wph
    @2
    cA
    cV
    smfmullem4.a
    @27
    ssexd
    #
    @7
    eqid
    subsalsal
    #
    adantr
    @40
    vx
    @2
    cB
    @16
    cS
    @15
    cvv
    cr
    wph
    @33
    vx
    smfmullem4.x
    @33
    vx
    nfv
    #
    nfan
    #
    wph
    cS
    csalg
    wcel
    @33
    smfmullem4.s
    adantr
    #
    wph
    @2
    cvv
    wcel
    @33
    @44
    adantr
    #
    wph
    @11
    @26
    @33
    @28
    adantlr
    wph
    vx
    @2
    cB
    cmpt
    cS
    csmblfn
    cfv
    #
    wcel
    @33
    wph
    vx
    cA
    cB
    @2
    cS
    smfmullem4.s
    smfmullem4.m
    @27
    sssmfmpt
    adantr
    @40
    @15
    @33
    @15
    cr
    wcel
    wph
    @33
    cc0
    c3
    cfz
    co
    #
    cr
    cc0
    @4
    @33
    @4
    cr
    @51
    cmap
    co
    #
    wcel
    @51
    cr
    @4
    wf
    @33
    cK
    @52
    @4
    cK
    cq
    @51
    cmap
    co
    #
    @52
    cK
    vu
    cv
    #
    vv
    cv
    #
    cmul
    co
    #
    cR
    clt
    wbr
    #
    vv
    @21
    wral
    #
    vu
    @17
    wral
    #
    vq
    @53
    crab
    #
    @53
    smfmullem4.k
    @59
    vq
    @53
    ssrab2
    eqsstri
    #
    cr
    cvv
    wcel
    #
    cq
    cr
    wss
    @53
    @52
    wss
    reex
    qssre
    cq
    cr
    @51
    cvv
    mapss
    mp2an
    sstri
    @33
    id
    #
    sseldi
    @33
    cr
    @51
    @4
    cvv
    cvv
    @62
    @33
    reex
    a1i
    @33
    cc0
    c3
    cfz
    ovexd
    elmapd
    mpbid
    #
    cc0
    @51
    wcel
    #
    @33
    c3
    cc0
    cuz
    cfv
    wcel
    #
    @65
    @66
    cc0
    cz
    wcel
    #
    c3
    cz
    wcel
    #
    cc0
    c3
    cle
    wbr
    #
    w3a
    @67
    @68
    @69
    0z
    3z
    cc0
    c3
    0re
    3re
    3pos
    ltleii
    3pm3.2i
    cc0
    c3
    eluz2
    mpbir
    #
    cc0
    c3
    eluzfz1
    ax-mp
    a1i
    ffvelrnd
    adantl
    rexrd
    @40
    @16
    @33
    @16
    cr
    wcel
    wph
    @33
    @51
    cr
    c1
    @4
    @64
    c1
    @51
    wcel
    #
    @33
    @71
    cc0
    c1
    cle
    wbr
    #
    c1
    c3
    cle
    wbr
    #
    wa
    #
    @72
    @73
    0le1
    c1
    c3
    1re
    3re
    1lt3
    ltleii
    pm3.2i
    c1
    cz
    wcel
    @67
    @68
    @71
    @74
    wb
    1z
    0z
    3z
    c1
    cc0
    c3
    elfz
    mp3an
    mpbir
    a1i
    ffvelrnd
    adantl
    rexrd
    smfpimioompt
    @40
    vx
    @2
    cD
    @20
    cS
    @19
    cvv
    cr
    @47
    @48
    @49
    wph
    @11
    @29
    @33
    @32
    adantlr
    wph
    vx
    @2
    cD
    cmpt
    @50
    wcel
    @33
    wph
    vx
    cC
    cD
    @2
    cS
    smfmullem4.s
    smfmullem4.n
    wph
    vx
    @2
    cC
    smfmullem4.x
    @31
    ssdf
    sssmfmpt
    adantr
    @40
    @19
    @33
    @19
    cr
    wcel
    wph
    @33
    @51
    cr
    c2
    @4
    @64
    c2
    @51
    wcel
    #
    @33
    @75
    cc0
    c2
    cle
    wbr
    #
    c2
    c3
    cle
    wbr
    #
    wa
    #
    @76
    @77
    0le2
    c2
    c3
    2re
    3re
    2lt3
    ltleii
    pm3.2i
    c2
    cz
    wcel
    @67
    @68
    @75
    @78
    wb
    2z
    0z
    3z
    c2
    cc0
    c3
    elfz
    mp3an
    mpbir
    a1i
    ffvelrnd
    adantl
    rexrd
    @40
    @20
    @33
    @20
    cr
    wcel
    wph
    @33
    @51
    cr
    c3
    @4
    @64
    c3
    @51
    wcel
    #
    @33
    @66
    @79
    @70
    cc0
    c3
    eluzfz2
    ax-mp
    a1i
    ffvelrnd
    adantl
    rexrd
    smfpimioompt
    salincld
    syl5eqelr
    #
    elexd
    fvmpt2d
    #
    eqcomd
    adantlr
    adantr
    eleqtrd
    ex
    3adantl3
    reximdva
    mpd
    vq
    @8
    cK
    @5
    eliun
    sylibr
    3exp
    ralrimi
    @1
    vx
    @2
    @6
    vq
    vx
    cK
    @5
    vx
    vq
    cK
    @46
    nfci
    #
    vx
    @4
    cE
    vx
    cE
    @41
    smfmullem4.e
    vx
    vq
    cK
    @36
    @82
    @23
    vx
    @2
    nfrab1
    nfmpt
    nfcxfr
    vx
    @4
    nfcv
    nffv
    #
    nfiun
    rabssf
    sylibr
    wph
    vq
    cK
    @5
    @3
    @40
    @5
    @2
    wss
    #
    @1
    vx
    @5
    wral
    #
    wa
    @5
    @3
    wss
    @40
    @84
    @85
    @40
    @5
    @36
    @2
    @81
    @23
    vx
    @2
    ssrab2
    syl6eqss
    @40
    @1
    vx
    @5
    @47
    @40
    @13
    @1
    @40
    @13
    wa
    #
    @22
    cB
    @55
    cmul
    co
    #
    cR
    clt
    wbr
    #
    vv
    @21
    wral
    #
    @1
    @86
    @18
    @22
    @86
    @37
    @23
    @86
    @8
    @5
    @36
    @40
    @13
    simpr
    @40
    @5
    @36
    wceq
    @13
    @81
    adantr
    eleqtrd
    @23
    vx
    @2
    rabidim2
    syl
    #
    simprd
    @86
    @18
    @59
    @89
    @86
    @18
    @22
    @90
    simpld
    @33
    @59
    wph
    @13
    @33
    @4
    @60
    wcel
    @59
    @33
    @4
    cK
    @60
    @63
    smfmullem4.k
    syl6eleq
    @59
    vq
    @53
    rabidim2
    syl
    ad2antlr
    @58
    @89
    vu
    cB
    @17
    @54
    cB
    wceq
    #
    @57
    @88
    vv
    @21
    @91
    @56
    @87
    cR
    clt
    @54
    cB
    @55
    cmul
    oveq1
    breq1d
    ralbidv
    rspcva
    syl2anc
    @88
    @1
    vv
    cD
    @21
    @55
    cD
    wceq
    @87
    @0
    cR
    clt
    @55
    cD
    cB
    cmul
    oveq2
    breq1d
    rspcva
    syl2anc
    ex
    ralrimi
    jca
    @1
    vx
    @2
    @5
    @83
    vx
    @2
    nfcv
    ssrabf
    sylibr
    iunssd
    eqssd
    wph
    @7
    vq
    @5
    cK
    @45
    cK
    com
    cdom
    wbr
    #
    wph
    cK
    @53
    cdom
    wbr
    #
    @53
    com
    cdom
    wbr
    #
    @92
    cK
    @53
    wss
    #
    @93
    @61
    @53
    cvv
    wcel
    @95
    @93
    wi
    cq
    @51
    cmap
    ovex
    cK
    @53
    cvv
    ssdomg
    ax-mp
    ax-mp
    @94
    wtru
    cq
    @51
    cq
    com
    cdom
    wbr
    wtru
    qct
    a1i
    wtru
    cc0
    c3
    fzfid
    mpct
    trud
    cK
    @53
    com
    domtr
    mp2an
    a1i
    wph
    cK
    @7
    @4
    cE
    wph
    vq
    cK
    @36
    @7
    cE
    @80
    smfmullem4.e
    fmptd
    ffvelrnda
    saliuncl
    eqeltrd
end
