include "citg1.mm"
include "cfv.mm"
include "crn.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "ccnv.mm"
include "cima.mm"
include "cvol.mm"
include "cmul.mm"
include "co.mm"
include "csu.mm"
include "cdm.mm"
include "wcel.mm"
include "wceq.mm"
include "itg1val.mm"
include "syl.mm"
include "wa.mm"
include "covol.mm"
include "cr.mm"
include "wss.mm"
include "wfn.mm"
include "wb.mm"
include "wf.mm"
include "i1ff.mm"
include "ffn.mm"
include "adantr.mm"
include "fniniseg.mm"
include "wne.mm"
include "eldifsni.mm"
include "ad2antlr.mm"
include "wn.mm"
include "simprl.mm"
include "eldif.mm"
include "simplrr.mm"
include "simpll.mm"
include "sylan.mm"
include "eqtr3d.mm"
include "ex.mm"
include "syl5bir.mm"
include "mpand.mm"
include "necon1ad.mm"
include "mpd.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "sstrd.mm"
include "ovolssnul.mm"
include "syl3anc.mm"
include "nulmbl.mm"
include "syl2anc.mm"
include "mblvol.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "frn.mm"
include "ssdifssd.mm"
include "sselda.mm"
include "recnd.mm"
include "mul01d.mm"
include "sumeq2dv.mm"
include "cuz.mm"
include "cfn.mm"
include "wo.mm"
include "i1frn.mm"
include "difss.mm"
include "ssfi.mm"
include "sylancl.mm"
include "olcd.mm"
include "sumz.mm"

theorem itg10a
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vk: setvar k
  let cG: class G
  assume itg10a.1: |- ( ph -> F e. dom S.1 )
  assume itg10a.2: |- ( ph -> A C_ RR )
  assume itg10a.3: |- ( ph -> ( vol* ` A ) = 0 )
  assume itg10a.4: |- ( ( ph /\ x e. ( RR \ A ) ) -> ( F ` x ) = 0 )

  disjoint A x
  disjoint F x
  disjoint ph x
  disjoint k x
  disjoint F k
  disjoint G x
  disjoint k ph
  assert |- ( ph -> ( S.1 ` F ) = 0 )

  proof
    wph
    cF
    citg1
    cfv
    #
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
    @4
    csn
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
    cc0
    wph
    cF
    citg1
    cdm
    wcel
    #
    @0
    @8
    wceq
    itg10a.1
    vk
    cF
    itg1val
    syl
    wph
    @8
    @3
    cc0
    vk
    csu
    #
    cc0
    wph
    @3
    @7
    cc0
    vk
    wph
    @4
    @3
    wcel
    #
    wa
    #
    @7
    @4
    cc0
    cmul
    co
    cc0
    @12
    @6
    cc0
    @4
    cmul
    @12
    @6
    @5
    covol
    cfv
    #
    cc0
    @12
    @5
    cvol
    cdm
    wcel
    #
    @6
    @13
    wceq
    @12
    @5
    cr
    wss
    @13
    cc0
    wceq
    #
    @14
    @12
    @5
    cA
    cr
    @12
    vx
    @5
    cA
    @12
    vx
    cv
    #
    @5
    wcel
    #
    @16
    cr
    wcel
    #
    @16
    cF
    cfv
    #
    @4
    wceq
    #
    wa
    #
    @16
    cA
    wcel
    #
    @12
    cF
    cr
    wfn
    #
    @17
    @21
    wb
    wph
    @23
    @11
    wph
    cr
    cr
    cF
    wf
    #
    @23
    wph
    @9
    @24
    itg10a.1
    cF
    i1ff
    syl
    #
    cr
    cr
    cF
    ffn
    syl
    adantr
    cr
    @4
    @16
    cF
    fniniseg
    syl
    @12
    @21
    @22
    @12
    @21
    wa
    #
    @4
    cc0
    wne
    #
    @22
    @11
    @27
    wph
    @21
    @4
    @1
    cc0
    eldifsni
    ad2antlr
    @26
    @22
    @4
    cc0
    @26
    @18
    @22
    wn
    #
    @4
    cc0
    wceq
    #
    @12
    @18
    @20
    simprl
    @18
    @28
    wa
    @16
    cr
    cA
    cdif
    wcel
    #
    @26
    @29
    @16
    cr
    cA
    eldif
    @26
    @30
    @29
    @26
    @30
    wa
    @19
    @4
    cc0
    @12
    @18
    @20
    @30
    simplrr
    @26
    wph
    @30
    @19
    cc0
    wceq
    wph
    @11
    @21
    simpll
    itg10a.4
    sylan
    eqtr3d
    ex
    syl5bir
    mpand
    necon1ad
    mpd
    ex
    sylbid
    ssrdv
    #
    wph
    cA
    cr
    wss
    #
    @11
    itg10a.2
    adantr
    #
    sstrd
    @12
    @5
    cA
    wss
    @32
    cA
    covol
    cfv
    cc0
    wceq
    #
    @15
    @31
    @33
    wph
    @34
    @11
    itg10a.3
    adantr
    @5
    cA
    ovolssnul
    syl3anc
    #
    @5
    nulmbl
    syl2anc
    @5
    mblvol
    syl
    @35
    eqtrd
    oveq2d
    @12
    @4
    @12
    @4
    wph
    @3
    cr
    @4
    wph
    @1
    cr
    @2
    wph
    @24
    @1
    cr
    wss
    @25
    cr
    cr
    cF
    frn
    syl
    ssdifssd
    sselda
    recnd
    mul01d
    eqtrd
    sumeq2dv
    wph
    @3
    cc0
    cuz
    cfv
    wss
    #
    @3
    cfn
    wcel
    #
    wo
    @10
    cc0
    wceq
    wph
    @37
    @36
    wph
    @1
    cfn
    wcel
    #
    @3
    @1
    wss
    @37
    wph
    @9
    @38
    itg10a.1
    cF
    i1frn
    syl
    @1
    @2
    difss
    @1
    @3
    ssfi
    sylancl
    olcd
    @3
    vk
    cc0
    sumz
    syl
    eqtrd
    eqtrd
end
