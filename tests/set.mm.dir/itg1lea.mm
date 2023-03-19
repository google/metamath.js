include "cc0.mm"
include "citg1.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cof.mm"
include "cdm.mm"
include "wcel.mm"
include "i1fsub.mm"
include "syl2anc.mm"
include "cv.mm"
include "cr.mm"
include "cdif.mm"
include "wa.mm"
include "wb.mm"
include "eldifi.mm"
include "wf.mm"
include "i1ff.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "subge0d.mm"
include "sylan2.mm"
include "mpbird.mm"
include "wceq.mm"
include "cvv.mm"
include "wfn.mm"
include "ffn.mm"
include "reex.mm"
include "a1i.mm"
include "inidm.mm"
include "eqidd.mm"
include "ofval.mm"
include "breqtrrd.mm"
include "itg1ge0a.mm"
include "itg1sub.mm"
include "breqtrd.mm"
include "itg1cl.mm"
include "mpbid.mm"

theorem itg1lea
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cG: class G
  let vk: setvar k
  assume itg10a.1: |- ( ph -> F e. dom S.1 )
  assume itg10a.2: |- ( ph -> A C_ RR )
  assume itg10a.3: |- ( ph -> ( vol* ` A ) = 0 )
  assume itg1lea.4: |- ( ph -> G e. dom S.1 )
  assume itg1lea.5: |- ( ( ph /\ x e. ( RR \ A ) ) -> ( F ` x ) <_ ( G ` x ) )

  disjoint A x
  disjoint F x
  disjoint G x
  disjoint ph x
  disjoint k x
  disjoint F k
  disjoint k ph
  assert |- ( ph -> ( S.1 ` F ) <_ ( S.1 ` G ) )

  proof
    wph
    cc0
    cG
    citg1
    cfv
    #
    cF
    citg1
    cfv
    #
    cmin
    co
    #
    cle
    wbr
    @1
    @0
    cle
    wbr
    wph
    cc0
    cG
    cF
    cmin
    cof
    co
    #
    citg1
    cfv
    #
    @2
    cle
    wph
    vx
    cA
    @3
    wph
    cG
    citg1
    cdm
    #
    wcel
    #
    cF
    @5
    wcel
    #
    @3
    @5
    wcel
    itg1lea.4
    itg10a.1
    cG
    cF
    i1fsub
    syl2anc
    itg10a.2
    itg10a.3
    wph
    vx
    cv
    #
    cr
    cA
    cdif
    wcel
    #
    wa
    #
    cc0
    @8
    cG
    cfv
    #
    @8
    cF
    cfv
    #
    cmin
    co
    #
    @8
    @3
    cfv
    #
    cle
    @10
    cc0
    @13
    cle
    wbr
    #
    @12
    @11
    cle
    wbr
    #
    itg1lea.5
    @9
    wph
    @8
    cr
    wcel
    #
    @15
    @16
    wb
    @8
    cr
    cA
    eldifi
    #
    wph
    @17
    wa
    #
    @11
    @12
    wph
    cr
    cr
    @8
    cG
    wph
    @6
    cr
    cr
    cG
    wf
    #
    itg1lea.4
    cG
    i1ff
    syl
    #
    ffvelrnda
    wph
    cr
    cr
    @8
    cF
    wph
    @7
    cr
    cr
    cF
    wf
    #
    itg10a.1
    cF
    i1ff
    syl
    #
    ffvelrnda
    subge0d
    sylan2
    mpbird
    @9
    wph
    @17
    @14
    @13
    wceq
    @18
    wph
    cr
    cr
    @11
    @12
    cmin
    cr
    cG
    cF
    cvv
    cvv
    @8
    wph
    @20
    cG
    cr
    wfn
    @21
    cr
    cr
    cG
    ffn
    syl
    wph
    @22
    cF
    cr
    wfn
    @23
    cr
    cr
    cF
    ffn
    syl
    cr
    cvv
    wcel
    wph
    reex
    a1i
    #
    @24
    cr
    inidm
    @19
    @11
    eqidd
    @19
    @12
    eqidd
    ofval
    sylan2
    breqtrrd
    itg1ge0a
    wph
    @6
    @7
    @4
    @2
    wceq
    itg1lea.4
    itg10a.1
    cG
    cF
    itg1sub
    syl2anc
    breqtrd
    wph
    @0
    @1
    wph
    @6
    @0
    cr
    wcel
    itg1lea.4
    cG
    itg1cl
    syl
    wph
    @7
    @1
    cr
    wcel
    itg10a.1
    cF
    itg1cl
    syl
    subge0d
    mpbid
end
