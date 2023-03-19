include "cc0.mm"
include "crn.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "ccnv.mm"
include "cima.mm"
include "cvol.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "csu.mm"
include "citg1.mm"
include "cle.mm"
include "cfn.mm"
include "wcel.mm"
include "wss.mm"
include "cdm.mm"
include "i1frn.mm"
include "syl.mm"
include "difss.mm"
include "ssfi.mm"
include "sylancl.mm"
include "wa.mm"
include "cr.mm"
include "wf.mm"
include "i1ff.mm"
include "frn.mm"
include "ssdifssd.mm"
include "sselda.mm"
include "i1fima2sn.mm"
include "sylan.mm"
include "remulcld.mm"
include "wbr.mm"
include "clt.mm"
include "0le0.mm"
include "covol.mm"
include "wceq.mm"
include "i1fima.mm"
include "mblvol.mm"
include "ad2antrr.mm"
include "wb.mm"
include "wfn.mm"
include "ffn.mm"
include "fniniseg.mm"
include "wn.mm"
include "simprl.mm"
include "eldif.mm"
include "wi.mm"
include "ex.mm"
include "simprr.mm"
include "breq2d.mm"
include "0red.mm"
include "adantr.mm"
include "lenltd.mm"
include "bitrd.mm"
include "sylibd.mm"
include "syl5bir.mm"
include "mpand.mm"
include "con4d.mm"
include "impancom.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "ovolssnul.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "cc.mm"
include "recnd.mm"
include "mul01d.mm"
include "syl5breqr.mm"
include "simpr.mm"
include "mblss.mm"
include "ovolge0.mm"
include "breqtrrd.mm"
include "mulge0d.mm"
include "ltlecasei.mm"
include "fsumge0.mm"
include "itg1val.mm"

theorem itg1ge0a
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vk: setvar k
  let cG: class G
  assume itg10a.1: |- ( ph -> F e. dom S.1 )
  assume itg10a.2: |- ( ph -> A C_ RR )
  assume itg10a.3: |- ( ph -> ( vol* ` A ) = 0 )
  assume itg1ge0a.4: |- ( ( ph /\ x e. ( RR \ A ) ) -> 0 <_ ( F ` x ) )

  disjoint A x
  disjoint F x
  disjoint ph x
  disjoint k x
  disjoint F k
  disjoint G x
  disjoint k ph
  assert |- ( ph -> 0 <_ ( S.1 ` F ) )

  proof
    wph
    cc0
    cF
    crn
    #
    cc0
    csn
    #
    cdif
    #
    vk
    cv
    #
    cF
    ccnv
    @3
    csn
    #
    cima
    #
    cvol
    cfv
    #
    cmul
    co
    #
    vk
    csu
    #
    cF
    citg1
    cfv
    #
    cle
    wph
    @2
    @7
    vk
    wph
    @0
    cfn
    wcel
    #
    @2
    @0
    wss
    @2
    cfn
    wcel
    wph
    cF
    citg1
    cdm
    wcel
    #
    @10
    itg10a.1
    cF
    i1frn
    syl
    @0
    @1
    difss
    @0
    @2
    ssfi
    sylancl
    wph
    @3
    @2
    wcel
    #
    wa
    #
    @3
    @6
    wph
    @2
    cr
    @3
    wph
    @0
    cr
    @1
    wph
    cr
    cr
    cF
    wf
    #
    @0
    cr
    wss
    wph
    @11
    @14
    itg10a.1
    cF
    i1ff
    syl
    #
    cr
    cr
    cF
    frn
    syl
    ssdifssd
    sselda
    #
    wph
    @11
    @12
    @6
    cr
    wcel
    #
    itg10a.1
    @3
    @0
    cF
    i1fima2sn
    sylan
    #
    remulcld
    @13
    cc0
    @7
    cle
    wbr
    @3
    cc0
    @13
    @3
    cc0
    clt
    wbr
    #
    wa
    #
    cc0
    cc0
    @7
    cle
    0le0
    @20
    @7
    @3
    cc0
    cmul
    co
    cc0
    @20
    @6
    cc0
    @3
    cmul
    @20
    @6
    @5
    covol
    cfv
    #
    cc0
    wph
    @6
    @21
    wceq
    #
    @12
    @19
    wph
    @5
    cvol
    cdm
    wcel
    #
    @22
    wph
    @11
    @23
    itg10a.1
    @4
    cF
    i1fima
    syl
    #
    @5
    mblvol
    syl
    #
    ad2antrr
    @20
    @5
    cA
    wss
    cA
    cr
    wss
    #
    cA
    covol
    cfv
    cc0
    wceq
    #
    @21
    cc0
    wceq
    @20
    vx
    @5
    cA
    @20
    vx
    cv
    #
    @5
    wcel
    #
    @28
    cr
    wcel
    #
    @28
    cF
    cfv
    #
    @3
    wceq
    #
    wa
    #
    @28
    cA
    wcel
    #
    wph
    @29
    @33
    wb
    #
    @12
    @19
    wph
    cF
    cr
    wfn
    #
    @35
    wph
    @14
    @36
    @15
    cr
    cr
    cF
    ffn
    syl
    cr
    @3
    @28
    cF
    fniniseg
    syl
    ad2antrr
    @13
    @33
    @19
    @34
    @13
    @33
    wa
    #
    @34
    @19
    @37
    @30
    @34
    wn
    #
    @19
    wn
    #
    @13
    @30
    @32
    simprl
    @30
    @38
    wa
    @28
    cr
    cA
    cdif
    wcel
    #
    @37
    @39
    @28
    cr
    cA
    eldif
    @37
    @40
    cc0
    @31
    cle
    wbr
    #
    @39
    wph
    @40
    @41
    wi
    @12
    @33
    wph
    @40
    @41
    itg1ge0a.4
    ex
    ad2antrr
    @37
    @41
    cc0
    @3
    cle
    wbr
    #
    @39
    @37
    @31
    @3
    cc0
    cle
    @13
    @30
    @32
    simprr
    breq2d
    @37
    cc0
    @3
    @37
    0red
    @13
    @3
    cr
    wcel
    #
    @33
    @16
    adantr
    lenltd
    bitrd
    sylibd
    syl5bir
    mpand
    con4d
    impancom
    sylbid
    ssrdv
    wph
    @26
    @12
    @19
    itg10a.2
    ad2antrr
    wph
    @27
    @12
    @19
    itg10a.3
    ad2antrr
    @5
    cA
    ovolssnul
    syl3anc
    eqtrd
    oveq2d
    @20
    @3
    @13
    @3
    cc
    wcel
    @19
    @13
    @3
    @16
    recnd
    adantr
    mul01d
    eqtrd
    syl5breqr
    @13
    @42
    wa
    #
    @3
    @6
    @13
    @43
    @42
    @16
    adantr
    @13
    @17
    @42
    @18
    adantr
    @13
    @42
    simpr
    @44
    cc0
    @21
    @6
    cle
    @44
    @5
    cr
    wss
    #
    cc0
    @21
    cle
    wbr
    @44
    @23
    @45
    wph
    @23
    @12
    @42
    @24
    ad2antrr
    @5
    mblss
    syl
    @5
    ovolge0
    syl
    wph
    @22
    @12
    @42
    @25
    ad2antrr
    breqtrrd
    mulge0d
    @16
    @13
    0red
    ltlecasei
    fsumge0
    wph
    @11
    @9
    @8
    wceq
    itg10a.1
    vk
    cF
    itg1val
    syl
    breqtrrd
end
