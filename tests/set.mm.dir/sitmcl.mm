include "csitm.mm"
include "co.mm"
include "cds.mm"
include "cfv.mm"
include "cof.mm"
include "cxrs.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "cress.mm"
include "csitg.mm"
include "cxme.mm"
include "eqid.mm"
include "sitmfval.mm"
include "crefld.mm"
include "cr.mm"
include "cxp.mm"
include "cres.mm"
include "cle.mm"
include "cordt.mm"
include "crest.mm"
include "csigagen.mm"
include "cxmu.mm"
include "crrh.mm"
include "cvv.mm"
include "xrge0base.mm"
include "ctopn.mm"
include "xrge0topn.mm"
include "eqcomi.mm"
include "xrge00.mm"
include "wcel.mm"
include "cvsca.mm"
include "wceq.mm"
include "ovex.mm"
include "ax-xrsvsca.mm"
include "ressvsca.mm"
include "ax-mp.mm"
include "csca.mm"
include "ax-xrssca.mm"
include "resssca.mm"
include "fveq2i.mm"
include "ovexd.mm"
include "cbs.mm"
include "cdm.mm"
include "cuni.mm"
include "wf.mm"
include "c0g.mm"
include "sibff.mm"
include "wb.mm"
include "ctps.mm"
include "xmstps.mm"
include "tpsuni.mm"
include "3syl.mm"
include "feq3.mm"
include "syl.mm"
include "mpbird.mm"
include "cmeas.mm"
include "crn.mm"
include "dmexg.mm"
include "uniexg.mm"
include "ofresid.mm"
include "cpsmet.mm"
include "cxmt.mm"
include "xmsxmet.mm"
include "xmetpsmet.mm"
include "psmetxrge0.mm"
include "xrge0tps.mm"
include "a1i.mm"
include "cha.mm"
include "ct1.mm"
include "cmopn.mm"
include "xmstopn.mm"
include "methaus.mm"
include "eqeltrd.mm"
include "haust1.mm"
include "cmnd.mm"
include "mndidcl.mm"
include "xmet0.mm"
include "syl2anc.mm"
include "syl6eq.mm"
include "sibfof.mm"
include "rebase.mm"
include "xpeq12i.mm"
include "reseq2i.mm"
include "ccmn.mm"
include "xrge0cmn.mm"
include "crrext.mm"
include "rerrext.mm"
include "eqeltrri.mm"
include "cv.mm"
include "cico.mm"
include "cima.mm"
include "w3a.mm"
include "cid.mm"
include "rrhre.mm"
include "imaeq1i.mm"
include "wss.mm"
include "cxr.mm"
include "0re.mm"
include "pnfxr.mm"
include "icossre.mm"
include "mp2an.mm"
include "resiima.mm"
include "eqtri.mm"
include "icossicc.mm"
include "eqsstri.mm"
include "sseli.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "ge0xmulcl.mm"
include "sitgclg.mm"

theorem sitmcl
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cM: class M
  let cW: class W
  let vm: setvar m
  let vx: setvar x
  assume sitmcl.0: |- ( ph -> W e. Mnd )
  assume sitmcl.1: |- ( ph -> W e. *MetSp )
  assume sitmcl.2: |- ( ph -> M e. U. ran measures )
  assume sitmcl.3: |- ( ph -> F e. dom ( W sitg M ) )
  assume sitmcl.4: |- ( ph -> G e. dom ( W sitg M ) )


  assert |- ( ph -> ( F ( W sitm M ) G ) e. ( 0 [,] +oo ) )

  proof
    wph
    cF
    cG
    cW
    cM
    csitm
    co
    co
    cF
    cG
    cW
    cds
    cfv
    #
    cof
    co
    #
    cxrs
    cc0
    cpnf
    cicc
    co
    #
    cress
    co
    #
    cM
    csitg
    co
    #
    cfv
    @2
    wph
    @0
    cF
    cG
    cM
    cxme
    cW
    @0
    eqid
    sitmcl.1
    sitmcl.2
    sitmcl.3
    sitmcl.4
    sitmfval
    wph
    vx
    @2
    crefld
    cds
    cfv
    #
    cr
    cr
    cxp
    #
    cres
    cle
    cordt
    cfv
    @2
    crest
    co
    #
    csigagen
    cfv
    #
    cxmu
    vm
    @1
    crefld
    crefld
    crrh
    cfv
    #
    @7
    cM
    cvv
    @3
    cc0
    xrge0base
    @3
    ctopn
    cfv
    @7
    xrge0topn
    eqcomi
    @8
    eqid
    xrge00
    @2
    cvv
    wcel
    #
    cxmu
    @3
    cvsca
    cfv
    wceq
    cc0
    cpnf
    cicc
    ovex
    #
    @2
    cxmu
    cxrs
    @3
    cvv
    @3
    eqid
    #
    ax-xrsvsca
    ressvsca
    ax-mp
    crefld
    @3
    csca
    cfv
    #
    crrh
    @10
    crefld
    @13
    wceq
    @11
    @2
    crefld
    cxrs
    @3
    cvv
    @12
    ax-xrssca
    resssca
    ax-mp
    #
    fveq2i
    wph
    cxrs
    @2
    cress
    ovexd
    sitmcl.2
    wph
    @1
    cF
    cG
    @0
    cW
    cbs
    cfv
    #
    @15
    cxp
    #
    cres
    #
    cof
    co
    @4
    cdm
    wph
    cM
    cdm
    #
    cuni
    #
    @15
    @0
    cF
    cG
    cvv
    wph
    @19
    @15
    cF
    wf
    #
    @19
    cW
    ctopn
    cfv
    #
    cuni
    #
    cF
    wf
    #
    wph
    @15
    @21
    csigagen
    cfv
    #
    cW
    cvsca
    cfv
    #
    cF
    cW
    csca
    cfv
    crrh
    cfv
    #
    @21
    cM
    cxme
    cW
    cW
    c0g
    cfv
    #
    @15
    eqid
    #
    @21
    eqid
    #
    @24
    eqid
    #
    @27
    eqid
    #
    @25
    eqid
    #
    @26
    eqid
    #
    sitmcl.1
    sitmcl.2
    sitmcl.3
    sibff
    wph
    @15
    @22
    wceq
    #
    @20
    @23
    wb
    wph
    cW
    cxme
    wcel
    #
    cW
    ctps
    wcel
    #
    @34
    sitmcl.1
    cW
    xmstps
    #
    @15
    @21
    cW
    @28
    @29
    tpsuni
    3syl
    #
    @15
    @22
    @19
    cF
    feq3
    syl
    mpbird
    wph
    @19
    @15
    cG
    wf
    #
    @19
    @22
    cG
    wf
    #
    wph
    @15
    @24
    @25
    cG
    @26
    @21
    cM
    cxme
    cW
    @27
    @28
    @29
    @30
    @31
    @32
    @33
    sitmcl.1
    sitmcl.2
    sitmcl.4
    sibff
    wph
    @34
    @39
    @40
    wb
    @38
    @15
    @22
    @19
    cG
    feq3
    syl
    mpbird
    wph
    cM
    cmeas
    crn
    cuni
    #
    wcel
    @18
    cvv
    wcel
    @19
    cvv
    wcel
    sitmcl.2
    cM
    @41
    dmexg
    @18
    cvv
    uniexg
    3syl
    ofresid
    wph
    @15
    @2
    @17
    @24
    @25
    cF
    cG
    @26
    @21
    @3
    cM
    cxme
    cW
    @27
    @28
    @29
    @30
    @31
    @32
    @33
    sitmcl.1
    sitmcl.2
    sitmcl.3
    xrge0base
    wph
    @35
    @36
    sitmcl.1
    @37
    syl
    wph
    @17
    @15
    cpsmet
    cfv
    wcel
    #
    @16
    @2
    @17
    wf
    wph
    @35
    @17
    @15
    cxmt
    cfv
    wcel
    #
    @42
    sitmcl.1
    @17
    cW
    @15
    @28
    @17
    eqid
    #
    xmsxmet
    #
    @17
    @15
    xmetpsmet
    3syl
    @17
    @15
    psmetxrge0
    syl
    sitmcl.4
    @3
    ctps
    wcel
    wph
    xrge0tps
    a1i
    #
    wph
    @21
    cha
    wcel
    @21
    ct1
    wcel
    wph
    @21
    @17
    cmopn
    cfv
    #
    cha
    wph
    @35
    @21
    @47
    wceq
    sitmcl.1
    @17
    @21
    cW
    @15
    @29
    @28
    @44
    xmstopn
    syl
    wph
    @35
    @43
    @47
    cha
    wcel
    sitmcl.1
    @45
    @17
    @47
    @15
    @47
    eqid
    methaus
    3syl
    eqeltrd
    @21
    haust1
    syl
    wph
    @27
    @27
    @17
    co
    #
    cc0
    @3
    c0g
    cfv
    wph
    @43
    @27
    @15
    wcel
    #
    @48
    cc0
    wceq
    wph
    @35
    @43
    sitmcl.1
    @45
    syl
    wph
    cW
    cmnd
    wcel
    @49
    sitmcl.0
    @15
    cW
    @27
    @28
    @31
    mndidcl
    syl
    @27
    @17
    @15
    xmet0
    syl2anc
    xrge00
    syl6eq
    sibfof
    eqeltrd
    @14
    @6
    crefld
    cbs
    cfv
    #
    @50
    cxp
    @5
    cr
    @50
    cr
    @50
    rebase
    rebase
    xpeq12i
    reseq2i
    @46
    @3
    ccmn
    wcel
    wph
    xrge0cmn
    a1i
    @13
    crrext
    wcel
    wph
    crefld
    @13
    crrext
    @14
    rerrext
    eqeltrri
    a1i
    wph
    vm
    cv
    #
    @9
    cc0
    cpnf
    cico
    co
    #
    cima
    #
    wcel
    #
    vx
    cv
    #
    @2
    wcel
    #
    w3a
    @51
    @2
    wcel
    #
    @56
    @51
    @55
    cxmu
    co
    @2
    wcel
    @54
    wph
    @57
    @56
    @53
    @2
    @51
    @53
    @52
    @2
    @53
    cid
    cr
    cres
    #
    @52
    cima
    #
    @52
    @9
    @58
    @52
    rrhre
    imaeq1i
    @52
    cr
    wss
    #
    @59
    @52
    wceq
    cc0
    cr
    wcel
    cpnf
    cxr
    wcel
    @60
    0re
    pnfxr
    cc0
    cpnf
    icossre
    mp2an
    cr
    @52
    resiima
    ax-mp
    eqtri
    cc0
    cpnf
    icossicc
    eqsstri
    sseli
    3ad2ant2
    wph
    @54
    @56
    simp3
    @51
    @55
    ge0xmulcl
    syl2anc
    sitgclg
    eqeltrd
end
