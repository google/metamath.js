include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "cif.mm"
include "cfz.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "a1i.mm"
include "wor.mm"
include "ltso.mm"
include "fzfid.mm"
include "c0.mm"
include "wne.mm"
include "cuz.mm"
include "eqid.mm"
include "cceil.mm"
include "cz.mm"
include "ceilcl.mm"
include "syl.mm"
include "ifcld.mm"
include "eqeltrd.mm"
include "zred.mm"
include "max2.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "breqtrd.mm"
include "eluzd.mm"
include "eluzfz2.mm"
include "ne0i.mm"
include "wa.mm"
include "wf.mm"
include "adantr.mm"
include "elfzelz.mm"
include "adantl.mm"
include "elfzle1.mm"
include "syl6eleqr.mm"
include "ffvelrnd.mm"
include "fisupclrnmpt.mm"
include "syl5eqel.mm"
include "ffvelrnda.mm"
include "ad2antrr.mm"
include "simpll.mm"
include "eluzelz2.mm"
include "ad2antlr.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "eluzle.mm"
include "simpr.mm"
include "elfzd.mm"
include "fimaxre4.mm"
include "suprubrnmpt.mm"
include "syl6breqr.mm"
include "max1.mm"
include "letrd.mm"
include "wn.mm"
include "uzssre.mm"
include "eqsstri.mm"
include "sseli.mm"
include "sseldi.mm"
include "ceilge.mm"
include "ltnled.mm"
include "mpbird.mm"
include "lelttrd.mm"
include "ltled.mm"
include "wi.mm"
include "r19.21bi.mm"
include "mpd.mm"
include "syldan.mm"
include "pm2.61dan.mm"
include "ex.mm"
include "ralrimi.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfeq.mm"
include "breq2.mm"
include "ralbid.mm"
include "rspce.mm"

theorem limsupubuzlem
  let wph: wff ph
  let vx: setvar x
  let vj: setvar j
  let cF: class F
  let cK: class K
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vb: setvar b
  assume limsupubuzlem.j: |- F/ j ph
  assume limsupubuzlem.e: |- F/_ j X
  assume limsupubuzlem.m: |- ( ph -> M e. ZZ )
  assume limsupubuzlem.z: |- Z = ( ZZ>= ` M )
  assume limsupubuzlem.f: |- ( ph -> F : Z --> RR )
  assume limsupubuzlem.y: |- ( ph -> Y e. RR )
  assume limsupubuzlem.k: |- ( ph -> K e. RR )
  assume limsupubuzlem.b: |- ( ph -> A. j e. Z ( K <_ j -> ( F ` j ) <_ Y ) )
  assume limsupubuzlem.n: |- N = if ( ( |^ ` K ) <_ M , M , ( |^ ` K ) )
  assume limsupubuzlem.w: |- W = sup ( ran ( j e. ( M ... N ) |-> ( F ` j ) ) , RR , < )
  assume limsupubuzlem.x: |- X = if ( W <_ Y , Y , W )

  disjoint F x
  disjoint M j
  disjoint N j
  disjoint X x
  disjoint Z x
  disjoint j x
  disjoint F b
  disjoint M b
  disjoint b j
  disjoint N b
  disjoint b ph
  assert |- ( ph -> E. x e. RR A. j e. Z ( F ` j ) <_ x )

  proof
    wph
    cX
    cr
    wcel
    #
    vj
    cv
    #
    cF
    cfv
    #
    cX
    cle
    wbr
    #
    vj
    cZ
    wral
    #
    @2
    vx
    cv
    #
    cle
    wbr
    #
    vj
    cZ
    wral
    #
    vx
    cr
    wrex
    wph
    cX
    cW
    cY
    cle
    wbr
    #
    cY
    cW
    cif
    #
    cr
    limsupubuzlem.x
    wph
    @8
    cY
    cW
    cr
    limsupubuzlem.y
    wph
    cW
    vj
    cM
    cN
    cfz
    co
    #
    @2
    cmpt
    crn
    cr
    clt
    csup
    #
    cr
    cW
    @11
    wceq
    wph
    limsupubuzlem.w
    a1i
    wph
    vj
    cr
    @10
    @2
    clt
    limsupubuzlem.j
    cr
    clt
    wor
    wph
    ltso
    a1i
    wph
    cM
    cN
    fzfid
    #
    wph
    cN
    @10
    wcel
    #
    @10
    c0
    wne
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    @13
    wph
    cM
    cN
    @14
    @14
    eqid
    #
    limsupubuzlem.m
    wph
    cN
    cK
    cceil
    cfv
    #
    cM
    cle
    wbr
    #
    cM
    @16
    cif
    #
    cz
    cN
    @18
    wceq
    wph
    limsupubuzlem.n
    a1i
    #
    wph
    @17
    cM
    @16
    cz
    limsupubuzlem.m
    wph
    cK
    cr
    wcel
    #
    @16
    cz
    wcel
    limsupubuzlem.k
    cK
    ceilcl
    syl
    #
    ifcld
    eqeltrd
    #
    wph
    cM
    @18
    cN
    cle
    wph
    @16
    cr
    wcel
    #
    cM
    cr
    wcel
    #
    cM
    @18
    cle
    wbr
    wph
    @16
    @21
    zred
    #
    wph
    cM
    limsupubuzlem.m
    zred
    #
    @16
    cM
    max2
    syl2anc
    wph
    cN
    @18
    @19
    eqcomd
    #
    breqtrd
    eluzd
    #
    cM
    cN
    eluzfz2
    syl
    @10
    cN
    ne0i
    syl
    wph
    @1
    @10
    wcel
    #
    wa
    #
    cZ
    cr
    @1
    cF
    wph
    cZ
    cr
    cF
    wf
    @29
    limsupubuzlem.f
    adantr
    @30
    @1
    @14
    cZ
    @30
    cM
    @1
    @14
    @15
    wph
    cM
    cz
    wcel
    #
    @29
    limsupubuzlem.m
    adantr
    @29
    @1
    cz
    wcel
    #
    wph
    @1
    cM
    cN
    elfzelz
    adantl
    @29
    cM
    @1
    cle
    wbr
    #
    wph
    @1
    cM
    cN
    elfzle1
    adantl
    eluzd
    limsupubuzlem.z
    syl6eleqr
    ffvelrnd
    #
    fisupclrnmpt
    eqeltrd
    #
    ifcld
    syl5eqel
    #
    wph
    @3
    vj
    cZ
    limsupubuzlem.j
    wph
    @1
    cZ
    wcel
    #
    @3
    wph
    @37
    wa
    #
    @1
    cN
    cle
    wbr
    #
    @3
    @38
    @39
    wa
    #
    @2
    cW
    cX
    @38
    @2
    cr
    wcel
    #
    @39
    wph
    cZ
    cr
    @1
    cF
    limsupubuzlem.f
    ffvelrnda
    #
    adantr
    wph
    cW
    cr
    wcel
    #
    @37
    @39
    @35
    ad2antrr
    wph
    @0
    @37
    @39
    @36
    ad2antrr
    @40
    wph
    @29
    @2
    cW
    cle
    wbr
    wph
    @37
    @39
    simpll
    @40
    @1
    cM
    cN
    wph
    @31
    @37
    @39
    limsupubuzlem.m
    ad2antrr
    wph
    cN
    cz
    wcel
    @37
    @39
    @22
    ad2antrr
    @37
    @32
    wph
    @39
    cM
    @1
    cZ
    limsupubuzlem.z
    eluzelz2
    ad2antlr
    @37
    @33
    wph
    @39
    @37
    @1
    @14
    wcel
    #
    @33
    @37
    @44
    cZ
    @14
    @1
    limsupubuzlem.z
    eleq2i
    biimpi
    cM
    @1
    eluzle
    syl
    ad2antlr
    @38
    @39
    simpr
    elfzd
    @30
    @2
    @11
    cW
    cle
    wph
    vj
    vb
    @10
    @2
    limsupubuzlem.j
    @34
    wph
    vj
    vb
    @10
    @2
    limsupubuzlem.j
    @12
    @34
    fimaxre4
    suprubrnmpt
    limsupubuzlem.w
    syl6breqr
    syl2anc
    wph
    cW
    cX
    cle
    wbr
    @37
    @39
    wph
    cW
    @9
    cX
    cle
    wph
    @43
    cY
    cr
    wcel
    #
    cW
    @9
    cle
    wbr
    @35
    limsupubuzlem.y
    cW
    cY
    max1
    syl2anc
    limsupubuzlem.x
    syl6breqr
    ad2antrr
    letrd
    @38
    @39
    wn
    #
    cK
    @1
    cle
    wbr
    #
    @3
    @38
    @46
    wa
    #
    cK
    @1
    wph
    @20
    @37
    @46
    limsupubuzlem.k
    ad2antrr
    #
    @37
    @1
    cr
    wcel
    wph
    @46
    cZ
    cr
    @1
    cZ
    @14
    cr
    limsupubuzlem.z
    cM
    uzssre
    #
    eqsstri
    sseli
    ad2antlr
    #
    @48
    cK
    cN
    @1
    @49
    wph
    cN
    cr
    wcel
    @37
    @46
    wph
    @14
    cr
    cN
    @50
    @28
    sseldi
    #
    ad2antrr
    #
    @51
    wph
    cK
    cN
    cle
    wbr
    @37
    @46
    wph
    cK
    @16
    cN
    limsupubuzlem.k
    @25
    @52
    wph
    @20
    cK
    @16
    cle
    wbr
    limsupubuzlem.k
    cK
    ceilge
    syl
    wph
    @16
    @18
    cN
    cle
    wph
    @23
    @24
    @16
    @18
    cle
    wbr
    @25
    @26
    @16
    cM
    max1
    syl2anc
    @27
    breqtrd
    letrd
    ad2antrr
    @48
    cN
    @1
    clt
    wbr
    @46
    @38
    @46
    simpr
    @48
    cN
    @1
    @53
    @51
    ltnled
    mpbird
    lelttrd
    ltled
    @38
    @47
    wa
    #
    @2
    cY
    cX
    @38
    @41
    @47
    @42
    adantr
    wph
    @45
    @37
    @47
    limsupubuzlem.y
    ad2antrr
    wph
    @0
    @37
    @47
    @36
    ad2antrr
    @54
    @47
    @2
    cY
    cle
    wbr
    #
    @38
    @47
    simpr
    @38
    @47
    @55
    wi
    #
    @47
    wph
    @56
    vj
    cZ
    limsupubuzlem.b
    r19.21bi
    adantr
    mpd
    wph
    cY
    cX
    cle
    wbr
    @37
    @47
    wph
    cY
    @9
    cX
    cle
    wph
    @43
    @45
    cY
    @9
    cle
    wbr
    @35
    limsupubuzlem.y
    cW
    cY
    max2
    syl2anc
    limsupubuzlem.x
    syl6breqr
    ad2antrr
    letrd
    syldan
    pm2.61dan
    ex
    ralrimi
    @7
    @4
    vx
    cX
    cr
    @4
    vx
    nfv
    @5
    cX
    wceq
    @6
    @3
    vj
    cZ
    vj
    @5
    cX
    vj
    @5
    nfcv
    limsupubuzlem.e
    nfeq
    @5
    cX
    @2
    cle
    breq2
    ralbid
    rspce
    syl2anc
end
