include "cicc.mm"
include "co.mm"
include "cioo.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "csn.mm"
include "cun.mm"
include "crest.mm"
include "wss.mm"
include "ioossicc.mm"
include "a1i.mm"
include "cr.mm"
include "cc.mm"
include "iccssred.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "eqid.mm"
include "cioc.mm"
include "cnt.mm"
include "crn.mm"
include "ctg.mm"
include "cdif.mm"
include "cin.mm"
include "cpnf.mm"
include "ctop.mm"
include "wcel.mm"
include "cuni.mm"
include "retop.mm"
include "cxr.mm"
include "rexrd.mm"
include "iocssre.mm"
include "syl2anc.mm"
include "difssd.mm"
include "unssd.mm"
include "uniretop.mm"
include "syl6sseq.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "wo.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "elioore.mm"
include "ad2antlr.mm"
include "w3a.mm"
include "simplr.mm"
include "wb.mm"
include "ad2antrr.mm"
include "pnfxr.mm"
include "elioo2.mm"
include "sylancl.mm"
include "mpbid.mm"
include "simp2d.mm"
include "simpr.mm"
include "elioc2.mm"
include "mpbir3and.mm"
include "orcd.mm"
include "wn.mm"
include "w3o.mm"
include "3mix3.mm"
include "3ianor.mm"
include "sylibr.mm"
include "adantl.mm"
include "elicc2.mm"
include "mtbird.mm"
include "eldifd.mm"
include "olcd.mm"
include "pm2.61dan.mm"
include "elun.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "ntrss.mm"
include "syl3anc.mm"
include "ltpnfd.mm"
include "eliood.mm"
include "wceq.mm"
include "iooretop.mm"
include "isopn3i.mm"
include "eleqtrrd.mm"
include "sseldd.mm"
include "ltled.mm"
include "ubicc2.mm"
include "elind.mm"
include "iocssicc.mm"
include "restntr.mm"
include "rerest.mm"
include "syl.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "eleqtrd.mm"
include "snssd.mm"
include "ssequn2.mm"
include "sylib.mm"
include "oveq2d.mm"
include "snunioo2.mm"
include "fveq12d.mm"
include "limcres.mm"

theorem limcicciooub
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  assume limcicciooub.1: |- ( ph -> A e. RR )
  assume limcicciooub.2: |- ( ph -> B e. RR )
  assume limcicciooub.3: |- ( ph -> A < B )
  assume limcicciooub.4: |- ( ph -> F : ( A [,] B ) --> CC )


  assert |- ( ph -> ( ( F |` ( A (,) B ) ) limCC B ) = ( F limCC B ) )

  proof
    wph
    cA
    cB
    cicc
    co
    #
    cB
    cA
    cB
    cioo
    co
    #
    cF
    ccnfld
    ctopn
    cfv
    #
    @0
    cB
    csn
    #
    cun
    #
    crest
    co
    #
    @2
    limcicciooub.4
    @1
    @0
    wss
    wph
    cA
    cB
    ioossicc
    a1i
    wph
    @0
    cr
    cc
    wph
    cA
    cB
    limcicciooub.1
    limcicciooub.2
    iccssred
    #
    ax-resscn
    syl6ss
    @2
    eqid
    #
    @5
    eqid
    wph
    cB
    cA
    cB
    cioc
    co
    #
    @2
    @0
    crest
    co
    #
    cnt
    cfv
    #
    cfv
    #
    @1
    @3
    cun
    #
    @5
    cnt
    cfv
    #
    cfv
    wph
    cB
    @8
    cioo
    crn
    ctg
    cfv
    #
    @0
    crest
    co
    #
    cnt
    cfv
    #
    cfv
    #
    @11
    wph
    cB
    @8
    cr
    @0
    cdif
    #
    cun
    #
    @14
    cnt
    cfv
    #
    cfv
    #
    @0
    cin
    #
    @17
    wph
    @21
    @0
    cB
    wph
    cA
    cpnf
    cioo
    co
    #
    @20
    cfv
    #
    @21
    cB
    wph
    @14
    ctop
    wcel
    #
    @19
    @14
    cuni
    #
    wss
    @23
    @19
    wss
    #
    @24
    @21
    wss
    @25
    wph
    retop
    a1i
    #
    wph
    @19
    cr
    @26
    wph
    @8
    @18
    cr
    wph
    cA
    cxr
    wcel
    #
    cB
    cr
    wcel
    #
    @8
    cr
    wss
    wph
    cA
    limcicciooub.1
    rexrd
    #
    limcicciooub.2
    cA
    cB
    iocssre
    syl2anc
    wph
    cr
    @0
    difssd
    unssd
    uniretop
    syl6sseq
    wph
    vx
    cv
    #
    @19
    wcel
    #
    vx
    @23
    wral
    @27
    wph
    @33
    vx
    @23
    wph
    @32
    @23
    wcel
    #
    wa
    #
    @32
    @8
    wcel
    #
    @32
    @18
    wcel
    #
    wo
    #
    @33
    @35
    @32
    cB
    cle
    wbr
    #
    @38
    @35
    @39
    wa
    #
    @36
    @37
    @40
    @36
    @32
    cr
    wcel
    #
    cA
    @32
    clt
    wbr
    #
    @39
    @34
    @41
    wph
    @39
    @32
    cA
    cpnf
    elioore
    #
    ad2antlr
    @40
    @41
    @42
    @32
    cpnf
    clt
    wbr
    #
    @40
    @34
    @41
    @42
    @44
    w3a
    #
    wph
    @34
    @39
    simplr
    @40
    @29
    cpnf
    cxr
    wcel
    #
    @34
    @45
    wb
    wph
    @29
    @34
    @39
    @31
    ad2antrr
    #
    pnfxr
    cA
    cpnf
    @32
    elioo2
    sylancl
    mpbid
    simp2d
    @35
    @39
    simpr
    @40
    @29
    @30
    @36
    @41
    @42
    @39
    w3a
    wb
    @47
    wph
    @30
    @34
    @39
    limcicciooub.2
    ad2antrr
    cA
    cB
    @32
    elioc2
    syl2anc
    mpbir3and
    orcd
    @35
    @39
    wn
    #
    wa
    #
    @37
    @36
    @49
    @32
    cr
    @0
    @34
    @41
    wph
    @48
    @43
    ad2antlr
    @49
    @32
    @0
    wcel
    #
    @41
    cA
    @32
    cle
    wbr
    #
    @39
    w3a
    #
    @48
    @52
    wn
    #
    @35
    @48
    @41
    wn
    #
    @51
    wn
    #
    @48
    w3o
    @53
    @48
    @54
    @55
    3mix3
    @41
    @51
    @39
    3ianor
    sylibr
    adantl
    @49
    cA
    cr
    wcel
    #
    @30
    @50
    @52
    wb
    wph
    @56
    @34
    @48
    limcicciooub.1
    ad2antrr
    wph
    @30
    @34
    @48
    limcicciooub.2
    ad2antrr
    cA
    cB
    @32
    elicc2
    syl2anc
    mtbird
    eldifd
    olcd
    pm2.61dan
    @32
    @8
    @18
    elun
    sylibr
    ralrimiva
    vx
    @23
    @19
    dfss3
    sylibr
    @19
    @23
    @14
    @26
    @26
    eqid
    ntrss
    syl3anc
    wph
    cB
    @23
    @24
    wph
    cA
    cpnf
    cB
    @31
    @46
    wph
    pnfxr
    a1i
    limcicciooub.2
    limcicciooub.3
    wph
    cB
    limcicciooub.2
    ltpnfd
    eliood
    wph
    @25
    @23
    @14
    wcel
    @24
    @23
    wceq
    @28
    cA
    cpnf
    iooretop
    @23
    @14
    isopn3i
    sylancl
    eleqtrrd
    sseldd
    wph
    @29
    cB
    cxr
    wcel
    #
    cA
    cB
    cle
    wbr
    cB
    @0
    wcel
    @31
    wph
    cB
    limcicciooub.2
    rexrd
    #
    wph
    cA
    cB
    limcicciooub.1
    limcicciooub.2
    limcicciooub.3
    ltled
    cA
    cB
    ubicc2
    syl3anc
    #
    elind
    wph
    @25
    @0
    cr
    wss
    #
    @8
    @0
    wss
    #
    @17
    @22
    wceq
    @28
    @6
    @61
    wph
    cA
    cB
    iocssicc
    a1i
    @8
    @14
    @15
    cr
    @0
    uniretop
    @15
    eqid
    restntr
    syl3anc
    eleqtrrd
    wph
    @8
    @16
    @10
    wph
    @15
    @9
    cnt
    wph
    @9
    @15
    wph
    @60
    @9
    @15
    wceq
    @6
    @0
    @14
    @2
    @7
    @14
    eqid
    rerest
    syl
    eqcomd
    fveq2d
    fveq1d
    eleqtrd
    wph
    @8
    @12
    @10
    @13
    wph
    @9
    @5
    cnt
    wph
    @0
    @4
    @2
    crest
    wph
    @4
    @0
    wph
    @3
    @0
    wss
    @4
    @0
    wceq
    wph
    cB
    @0
    @59
    snssd
    @3
    @0
    ssequn2
    sylib
    eqcomd
    oveq2d
    fveq2d
    wph
    @12
    @8
    wph
    @29
    @57
    cA
    cB
    clt
    wbr
    @12
    @8
    wceq
    @31
    @58
    limcicciooub.3
    cA
    cB
    snunioo2
    syl3anc
    eqcomd
    fveq12d
    eleqtrd
    limcres
end
