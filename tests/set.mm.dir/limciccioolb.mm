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
include "cico.mm"
include "cnt.mm"
include "crn.mm"
include "ctg.mm"
include "cdif.mm"
include "cin.mm"
include "cmnf.mm"
include "ctop.mm"
include "wcel.mm"
include "cuni.mm"
include "retop.mm"
include "cxr.mm"
include "rexrd.mm"
include "icossre.mm"
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
include "simpr.mm"
include "w3a.mm"
include "wb.mm"
include "mnfxr.mm"
include "adantr.mm"
include "elioo2.mm"
include "mpbid.mm"
include "simp3d.mm"
include "ad2antrr.mm"
include "elico2.mm"
include "mpbir3and.mm"
include "orcd.mm"
include "wn.mm"
include "intnanrd.mm"
include "elicc4.mm"
include "syl3anc.mm"
include "mtbird.mm"
include "eldifd.mm"
include "olcd.mm"
include "pm2.61dan.mm"
include "elun.mm"
include "sylibr.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "ntrss.mm"
include "mnfltd.mm"
include "eliood.mm"
include "wceq.mm"
include "iooretop.mm"
include "isopn3i.mm"
include "eleqtrrd.mm"
include "sseldd.mm"
include "leidd.mm"
include "ltled.mm"
include "eliccd.mm"
include "elind.mm"
include "icossicc.mm"
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
include "uncom.mm"
include "snunioo.mm"
include "syl5req.mm"
include "fveq12d.mm"
include "limcres.mm"

theorem limciccioolb
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  assume limciccioolb.1: |- ( ph -> A e. RR )
  assume limciccioolb.2: |- ( ph -> B e. RR )
  assume limciccioolb.3: |- ( ph -> A < B )
  assume limciccioolb.4: |- ( ph -> F : ( A [,] B ) --> CC )


  assert |- ( ph -> ( ( F |` ( A (,) B ) ) limCC A ) = ( F limCC A ) )

  proof
    wph
    cA
    cB
    cicc
    co
    #
    cA
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
    cA
    csn
    #
    cun
    #
    crest
    co
    #
    @2
    limciccioolb.4
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
    limciccioolb.1
    limciccioolb.2
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
    cA
    cA
    cB
    cico
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
    cA
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
    cA
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
    cA
    wph
    cmnf
    cB
    cioo
    co
    #
    @20
    cfv
    #
    @21
    cA
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
    cr
    wcel
    #
    cB
    cxr
    wcel
    #
    @8
    cr
    wss
    limciccioolb.1
    wph
    cB
    limciccioolb.2
    rexrd
    #
    cA
    cB
    icossre
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
    cA
    @32
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
    @39
    @32
    cB
    clt
    wbr
    #
    @34
    @41
    wph
    @39
    @32
    cmnf
    cB
    elioore
    #
    ad2antlr
    @35
    @39
    simpr
    @35
    @42
    @39
    @35
    @41
    cmnf
    @32
    clt
    wbr
    #
    @42
    @35
    @34
    @41
    @44
    @42
    w3a
    #
    wph
    @34
    simpr
    @35
    cmnf
    cxr
    wcel
    #
    @30
    @34
    @45
    wb
    @46
    @35
    mnfxr
    a1i
    wph
    @30
    @34
    @31
    adantr
    cmnf
    cB
    @32
    elioo2
    syl2anc
    mpbid
    simp3d
    adantr
    @40
    @29
    @30
    @36
    @41
    @39
    @42
    w3a
    wb
    wph
    @29
    @34
    @39
    limciccioolb.1
    ad2antrr
    wph
    @30
    @34
    @39
    @31
    ad2antrr
    cA
    cB
    @32
    elico2
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
    @48
    @32
    cr
    @0
    @34
    @41
    wph
    @47
    @43
    ad2antlr
    #
    @48
    @32
    @0
    wcel
    #
    @39
    @32
    cB
    cle
    wbr
    #
    wa
    #
    @48
    @39
    @51
    @35
    @47
    simpr
    intnanrd
    @48
    cA
    cxr
    wcel
    #
    @30
    @32
    cxr
    wcel
    @50
    @52
    wb
    wph
    @53
    @34
    @47
    wph
    cA
    limciccioolb.1
    rexrd
    #
    ad2antrr
    wph
    @30
    @34
    @47
    @31
    ad2antrr
    @48
    @32
    @49
    rexrd
    cA
    cB
    @32
    elicc4
    syl3anc
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
    cA
    @23
    @24
    wph
    cmnf
    cB
    cA
    @46
    wph
    mnfxr
    a1i
    @31
    limciccioolb.1
    wph
    cA
    limciccioolb.1
    mnfltd
    limciccioolb.3
    eliood
    wph
    @25
    @23
    @14
    wcel
    #
    @24
    @23
    wceq
    @28
    @55
    wph
    cmnf
    cB
    iooretop
    a1i
    @23
    @14
    isopn3i
    syl2anc
    eleqtrrd
    sseldd
    wph
    cA
    cB
    cA
    limciccioolb.1
    limciccioolb.2
    limciccioolb.1
    wph
    cA
    limciccioolb.1
    leidd
    wph
    cA
    cB
    limciccioolb.1
    limciccioolb.2
    limciccioolb.3
    ltled
    eliccd
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
    @58
    wph
    cA
    cB
    icossicc
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
    @57
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
    cA
    @0
    @56
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
    @3
    @1
    cun
    #
    @8
    @1
    @3
    uncom
    wph
    @53
    @30
    cA
    cB
    clt
    wbr
    @59
    @8
    wceq
    @54
    @31
    limciccioolb.3
    cA
    cB
    snunioo
    syl3anc
    syl5req
    fveq12d
    eleqtrd
    limcres
end
