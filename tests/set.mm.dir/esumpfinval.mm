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
include "cv.mm"
include "wa.mm"
include "cico.mm"
include "icossicc.mm"
include "sseldi.mm"
include "eqid.mm"
include "fmptd.mm"
include "cvv.mm"
include "c0ex.mm"
include "fsuppmptdm.mm"
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
include "cc.mm"
include "cr.mm"
include "rge0ssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "gsumfsum.mm"
include "3eqtr2d.mm"

theorem esumpfinval
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  assume esumpfinval.a: |- ( ph -> A e. Fin )
  assume esumpfinval.b: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,) +oo ) )

  disjoint A k
  disjoint k ph
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
    @7
    cA
    cB
    vk
    df-esum
    wph
    @8
    @6
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
    esumpfinval.a
    wph
    vk
    cA
    cB
    @1
    @3
    wph
    vk
    cv
    cA
    wcel
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
    esumpfinval.b
    sseldi
    @3
    eqid
    #
    fmptd
    wph
    vk
    cA
    @3
    @12
    cvv
    cB
    cc0
    @13
    esumpfinval.a
    esumpfinval.b
    cc0
    cvv
    wcel
    wph
    c0ex
    a1i
    fsuppmptdm
    @2
    ctopn
    cfv
    @10
    xrge0topn
    eqcomi
    @10
    cha
    wcel
    #
    wph
    @9
    cha
    wcel
    @1
    cvv
    wcel
    @14
    xrhaus
    cc0
    cpnf
    cicc
    ovex
    @1
    @9
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
    @12
    @3
    wf
    @5
    @4
    wceq
    esumpfinval.a
    wph
    vk
    cA
    cB
    @12
    @3
    esumpfinval.b
    @13
    fmptd
    cA
    @3
    cfn
    esumpfinvallem
    syl2anc
    wph
    cA
    cB
    vk
    esumpfinval.a
    @11
    @12
    cc
    cB
    @12
    cr
    cc
    rge0ssre
    ax-resscn
    sstri
    esumpfinval.b
    sseldi
    gsumfsum
    3eqtr2d
end
