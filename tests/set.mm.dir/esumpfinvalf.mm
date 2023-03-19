include "cesum.mm"
include "cxrs.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cress.mm"
include "cmpt.mm"
include "cgsu.mm"
include "ccnfld.mm"
include "csu.mm"
include "csn.mm"
include "cuni.mm"
include "ctsu.mm"
include "df-esum.mm"
include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "crest.mm"
include "cfn.mm"
include "xrge0base.mm"
include "xrge00.mm"
include "ccmn.mm"
include "wcel.mm"
include "xrge0cmn.mm"
include "a1i.mm"
include "ctps.mm"
include "xrge0tps.mm"
include "nfcv.mm"
include "cv.mm"
include "wa.mm"
include "cico.mm"
include "icossicc.mm"
include "sseldi.mm"
include "eqid.mm"
include "fmptdF.mm"
include "cvv.mm"
include "c0ex.mm"
include "fdmfifsupp.mm"
include "ctopn.mm"
include "xrge0topn.mm"
include "eqcomi.mm"
include "cha.mm"
include "xrhaus.mm"
include "ovex.mm"
include "resthaus.mm"
include "mp2an.mm"
include "haustsmsid.mm"
include "unieqd.mm"
include "syl5eq.mm"
include "unisn.mm"
include "syl6eq.mm"
include "wf.mm"
include "wceq.mm"
include "esumpfinvallem.mm"
include "syl2anc.mm"
include "csb.mm"
include "cc.mm"
include "wi.mm"
include "wsb.mm"
include "cr.mm"
include "rge0ssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "sbt.mm"
include "sbim.mm"
include "sban.mm"
include "sbf.mm"
include "clelsb3f.mm"
include "anbi12i.mm"
include "bitri.mm"
include "wsbc.mm"
include "sbsbc.mm"
include "wb.mm"
include "vex.mm"
include "sbcel1g.mm"
include "ax-mp.mm"
include "imbi12i.mm"
include "mpbi.mm"
include "gsumfsum.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvmptf.mm"
include "oveq2i.mm"
include "cbvsum.mm"
include "3eqtr4g.mm"
include "3eqtr2d.mm"

theorem esumpfinvalf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vl: setvar l
  assume esumpfinvalf.1: |- F/_ k A
  assume esumpfinvalf.2: |- F/ k ph
  assume esumpfinvalf.a: |- ( ph -> A e. Fin )
  assume esumpfinvalf.b: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,) +oo ) )


  assert |- ( ph -> sum* k e. A B = sum_ k e. A B )

  proof
    wph
    cA
    cB
    vk
    cesum
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
    vk
    cA
    cB
    cmpt
    #
    cgsu
    co
    #
    ccnfld
    @3
    cgsu
    co
    #
    cA
    cB
    vk
    csu
    #
    wph
    @0
    @4
    csn
    #
    cuni
    #
    @4
    wph
    @0
    @2
    @3
    ctsu
    co
    #
    cuni
    @8
    cA
    cB
    vk
    df-esum
    wph
    @9
    @7
    wph
    cA
    @1
    @3
    @2
    cle
    cordt
    cfv
    #
    @1
    crest
    co
    #
    cfn
    cc0
    xrge0base
    xrge00
    @2
    ccmn
    wcel
    wph
    xrge0cmn
    a1i
    @2
    ctps
    wcel
    wph
    xrge0tps
    a1i
    esumpfinvalf.a
    wph
    vk
    cA
    cB
    @1
    @3
    esumpfinvalf.2
    esumpfinvalf.1
    vk
    @1
    nfcv
    wph
    vk
    cv
    cA
    wcel
    #
    wa
    #
    cc0
    cpnf
    cico
    co
    #
    @1
    cB
    cc0
    cpnf
    icossicc
    esumpfinvalf.b
    sseldi
    @3
    eqid
    #
    fmptdF
    #
    wph
    cA
    @1
    @3
    cvv
    cc0
    @16
    esumpfinvalf.a
    cc0
    cvv
    wcel
    wph
    c0ex
    a1i
    fdmfifsupp
    @2
    ctopn
    cfv
    @11
    xrge0topn
    eqcomi
    @11
    cha
    wcel
    #
    wph
    @10
    cha
    wcel
    @1
    cvv
    wcel
    @17
    xrhaus
    cc0
    cpnf
    cicc
    ovex
    @1
    @10
    cvv
    resthaus
    mp2an
    a1i
    haustsmsid
    unieqd
    syl5eq
    @4
    @2
    @3
    cgsu
    ovex
    unisn
    syl6eq
    wph
    cA
    cfn
    wcel
    cA
    @14
    @3
    wf
    @5
    @4
    wceq
    esumpfinvalf.a
    wph
    vk
    cA
    cB
    @14
    @3
    esumpfinvalf.2
    esumpfinvalf.1
    vk
    @14
    nfcv
    esumpfinvalf.b
    @15
    fmptdF
    cA
    @3
    cfn
    esumpfinvallem
    syl2anc
    wph
    ccnfld
    vl
    cA
    vk
    vl
    cv
    #
    cB
    csb
    #
    cmpt
    #
    cgsu
    co
    cA
    @19
    vl
    csu
    @5
    @6
    wph
    cA
    @19
    vl
    esumpfinvalf.a
    @13
    cB
    cc
    wcel
    #
    wi
    #
    vk
    vl
    wsb
    #
    wph
    @18
    cA
    wcel
    #
    wa
    #
    @19
    cc
    wcel
    #
    wi
    #
    @22
    vk
    vl
    @13
    @14
    cc
    cB
    @14
    cr
    cc
    rge0ssre
    ax-resscn
    sstri
    esumpfinvalf.b
    sseldi
    sbt
    @23
    @13
    vk
    vl
    wsb
    #
    @21
    vk
    vl
    wsb
    #
    wi
    @27
    @13
    @21
    vk
    vl
    sbim
    @28
    @25
    @29
    @26
    @28
    wph
    vk
    vl
    wsb
    #
    @12
    vk
    vl
    wsb
    #
    wa
    @25
    wph
    @12
    vk
    vl
    sban
    @30
    wph
    @31
    @24
    wph
    vk
    vl
    esumpfinvalf.2
    sbf
    vl
    vk
    cA
    esumpfinvalf.1
    clelsb3f
    anbi12i
    bitri
    @29
    @21
    vk
    @18
    wsbc
    #
    @26
    @21
    vk
    vl
    sbsbc
    @18
    cvv
    wcel
    @32
    @26
    wb
    vl
    vex
    vk
    @18
    cB
    cc
    cvv
    sbcel1g
    ax-mp
    bitri
    imbi12i
    bitri
    mpbi
    gsumfsum
    @3
    @20
    ccnfld
    cgsu
    vk
    vl
    cA
    cB
    @19
    esumpfinvalf.1
    vl
    cA
    nfcv
    #
    vl
    cB
    nfcv
    #
    vk
    @18
    cB
    nfcsb1v
    #
    vk
    @18
    cB
    csbeq1a
    #
    cbvmptf
    oveq2i
    cA
    cB
    @19
    vk
    vl
    @36
    @33
    esumpfinvalf.1
    @34
    @35
    cbvsum
    3eqtr4g
    3eqtr2d
end
